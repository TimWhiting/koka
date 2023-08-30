import * as vscode from 'vscode'
import * as path from 'path'
import * as child_process from 'child_process'

import {
  LanguageClient,
  LanguageClientOptions,
  RevealOutputChannelOn,
  StreamInfo,
} from 'vscode-languageclient/node'

import { KokaConfig, scanForSDK } from './workspace'
import { CancellationToken, CodeLens, DebugConfiguration, DebugConfigurationProvider, EventEmitter, ProviderResult, TextDocument, WorkspaceFolder } from 'vscode'
import { KokaDebugSession } from './debugger'
import { AddressInfo, Server, createServer } from 'net'

let stderrOutputChannel: vscode.OutputChannel
let stdoutOutputChannel: vscode.OutputChannel
let languageServer: KokaLanguageServer;

export async function activate(context: vscode.ExtensionContext) {
  const vsConfig = vscode.workspace.getConfiguration('koka')
  // We can always create the client, as it does nothing as long as it is not started
  console.log(`Koka: language server enabled ${vsConfig.get('languageServer.enabled')}`)
  const { sdkPath, allSDKs } = scanForSDK()
  const config = new KokaConfig(vsConfig, sdkPath, allSDKs)
  if (!config.command) {
    vscode.window.showInformationMessage(`Koka SDK found but not working ${sdkPath}\n All SDKs: ${allSDKs}`)
    return
  }
  if (config.debugExtension) {
    stderrOutputChannel = vscode.window.createOutputChannel('Koka Language Server Stderr')
    stdoutOutputChannel = vscode.window.createOutputChannel('Koka Language Server Stdout')
    context.subscriptions.push(stderrOutputChannel)
    context.subscriptions.push(stdoutOutputChannel)
  }
  languageServer = new KokaLanguageServer()
  if (vsConfig.get('languageServer.enabled')) {
    await languageServer.start(config, context)
  }
  createCommands(context, vsConfig, config)

  // Debug Adaptor stuff
  context.subscriptions.push(vscode.commands.registerCommand('extension.language-koka.getProgramName', c => {
    return vscode.window.showInputBox({
      placeHolder: "Please enter the name of a koka file in the workspace folder",
      value: path.relative(config.cwd, vscode.window.activeTextEditor?.document.fileName || '') || 'test.kk'
    })
  }))

  // register a configuration provider for 'koka' debug type
  const provider = new KokaRunConfigurationProvider()
  context.subscriptions.push(vscode.debug.registerDebugConfigurationProvider('koka', provider))

  // debug adapters can be run in different ways by using a vscode.DebugAdapterDescriptorFactory:
  // run the debug adapter as a separate process
  let factory = new InlineDebugAdapterFactory(config)

  context.subscriptions.push(vscode.debug.registerDebugAdapterDescriptorFactory('koka', factory))


  const codeLensProvider = new MainCodeLensProvider(config)
  context.subscriptions.push(vscode.languages.registerCodeLensProvider({ language: "koka", scheme: "file" }, codeLensProvider))
}

class KokaLanguageServer {
  languageClient?: LanguageClient
  languageServerProcess?: child_process.ChildProcess
  socketServer?: Server
  outputChannel?: vscode.OutputChannel
  lspWriteEmitter: vscode.EventEmitter<string> = new vscode.EventEmitter<string>();
  lspPty?: vscode.Pseudoterminal
  lspTerminal?: vscode.Terminal

  showOutputChannel() {
    if (!this.lspTerminal?.exitStatus) {
      this.outputChannel?.show()
    } else if (this.lspPty) {
      this.lspTerminal = vscode.window.createTerminal({
        name: 'Koka Language Server',
        pty: this.lspPty,
        isTransient: true
      })
      this.lspTerminal.show()
    }
  }

  async start(config: KokaConfig, context: vscode.ExtensionContext) {
    console.log(`Koka: Language Server ${config.command} ${config.langServerArgs.join(" ")} Workspace: ${config.cwd}`)
    let self = this;
    function serverOptions(): Promise<StreamInfo> {
      return new Promise((resolve, reject) => {
        let timeout = setTimeout(() => {
          reject("Server took too long to connect")
        }, 2000)
        self.socketServer = createServer((s) => {
          console.log("Got Connection to Client")
          clearTimeout(timeout)
          resolve({ writer: s, reader: s })
        }).listen(0, "127.0.0.1", () => {
          console.log(`Starting language server in ${config.cwd}`)
          self.languageServerProcess = child_process.spawn(config.command, [...config.langServerArgs, "--lsport=" + (self.socketServer!.address() as AddressInfo).port], {
            cwd: config.cwd,
            env: process.env,
          })
          if (config.debugExtension) {
            self.languageServerProcess?.stderr?.on('data', (data) => {
              stderrOutputChannel.append(`${data.toString()}`)
            })
            self.languageServerProcess?.stdout?.on('data', (data) => {
              stdoutOutputChannel.append(`${data.toString()}`)
            })
          }
        })
      })
    }
    // This issue: https://github.com/microsoft/vscode/issues/571
    // This sample: https://github.com/ShMcK/vscode-pseudoterminal/blob/master/src/extension.ts
    this.lspPty = {
      onDidWrite: (listener) => this.lspWriteEmitter.event((e) => listener(e.replace('\r\n', '\n').replace('\n', '\r\n'))),
      open: () => { },
      close: () => { }
    };
    this.lspTerminal = vscode.window.createTerminal({
      name: 'Koka Language Server',
      pty: this.lspPty,
      isTransient: true
    })
    this.outputChannel = {
      name: 'Koka Language Server',
      append: (value: string) => this.lspWriteEmitter.fire(value),
      appendLine: (value: string) => {
        this.lspWriteEmitter.fire(value)
        this.lspWriteEmitter.fire('\r\n')
      },
      clear: () => {
        this.lspWriteEmitter.fire("\x1b[2J\x1b[3J\x1b[;H")
      },
      show: () => this.lspTerminal?.show(),
      hide: () => this.lspTerminal?.hide(),
      dispose: () => {
        this.lspTerminal?.dispose()
        this.lspWriteEmitter.dispose()
        this.lspPty?.close()
      },
      replace: (v) => {
        this.lspWriteEmitter.fire("\x1b[2J\x1b[3J\x1b[;H")
        this.lspWriteEmitter.fire(v)
      },

    };
    const clientOptions: LanguageClientOptions = {
      documentSelector: [{ language: 'koka', scheme: 'file' }],
      outputChannel: this.outputChannel,
      revealOutputChannelOn: RevealOutputChannelOn.Never,
    }
    this.languageClient = new LanguageClient(
      'Koka Language Client',
      serverOptions,
      clientOptions,
    )
    context.subscriptions.push(this)

    return await this.languageClient.start()
  }

  async dispose() {
    try {
      await this.languageClient?.stop()
      await this.languageClient?.dispose()
      this.languageServerProcess?.kill()
      this.socketServer?.close()
      // TODO: Does the terminal need to be disposed or is that handled by disposing the client
    } catch {
      // Ignore for now, the process should automatically die when the server / client closes the connection
    }
  }
}

export async function deactivate() {
}

function createCommands(
  context: vscode.ExtensionContext,
  config: vscode.WorkspaceConfiguration,
  kokaConfig: KokaConfig,
) {
  context.subscriptions.push(
    vscode.commands.registerCommand('koka.startWithoutDebugging', (resource: vscode.Uri) => {
      const launchConfig =
      {
        name: `koka run: ${resource.path}`,
        request: "launch",
        type: "koka",
        program: resource.path,
      }
      console.log(`Launch config ${launchConfig}`)
      vscode.debug.startDebugging(vscode.workspace.getWorkspaceFolder(resource), launchConfig as vscode.DebugConfiguration)
    }),
    vscode.commands.registerCommand('koka.restartLanguageServer', () => {
      if (!config.get('languageServer.enabled'))
        return vscode.window.showErrorMessage('Language server is not enabled')

      vscode.window.withProgress(
        {
          location: vscode.ProgressLocation.Notification,
          title: 'Koka',
          cancellable: false,
        },
        async (progress, token) => {
          progress.report({ message: 'Restarting language server' })
          await languageServer.dispose()
          const languageServerIdx = context.subscriptions.indexOf(languageServer)
          if (languageServerIdx != -1) {
            context.subscriptions.splice(languageServerIdx, 1)
          }

          const { sdkPath, allSDKs } = scanForSDK()
          const newConfig = new KokaConfig(config, sdkPath, allSDKs)
          languageServer = new KokaLanguageServer()
          await languageServer.start(newConfig, context)

          progress.report({
            message: 'Language server restarted',
            increment: 100,
          })
          // Wait 3 second to allow user to read message
          await new Promise((resolve) => setTimeout(resolve, 3000))
        },
      )
      vscode.window.createQuickPick
    }),
    vscode.commands.registerCommand('koka.selectSDK', async () => {
      const { sdkPath, allSDKs } = scanForSDK()
      kokaConfig.allSDKs = allSDKs
      const result = await vscode.window.showQuickPick(kokaConfig.allSDKs)
      if (result) kokaConfig.selectSDK(result)
      selectSDKMenuItem.tooltip = `${kokaConfig.sdkPath}`
      await vscode.commands.executeCommand('koka.restartLanguageServer')
    }),
    vscode.commands.registerCommand('koka.selectTarget', async () => {
      const result = await vscode.window.showQuickPick(['C', 'WASM', 'JS', 'C#'])
      if (result) kokaConfig.selectTarget(result)
      selectCompileTarget.text = `Koka Backend: ${kokaConfig.target}`
    }),
    vscode.commands.registerCommand('koka.showLSPOutput', async () => {
      languageServer.showOutputChannel()
    })
  )

  // create a new status bar item that we can now manage
  const selectSDKMenuItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Right, 100)
  selectSDKMenuItem.command = 'koka.selectSDK'
  context.subscriptions.push(selectSDKMenuItem)
  selectSDKMenuItem.show()
  selectSDKMenuItem.text = `Koka SDK`
  selectSDKMenuItem.tooltip = `${kokaConfig.sdkPath}`

  // create a new status bar item that we can now manage
  const selectCompileTarget = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Right, 100)
  selectCompileTarget.command = 'koka.selectTarget'
  context.subscriptions.push(selectCompileTarget)
  selectCompileTarget.show()
  selectCompileTarget.text = `Koka Backend: ${kokaConfig.target}`

}


class KokaRunConfigurationProvider implements DebugConfigurationProvider {

  /**
   * Massage a debug configuration just before a debug session is being launched,
   * e.g. add all missing attributes to the debug configuration.
   */
  resolveDebugConfiguration(folder: WorkspaceFolder | undefined, config: DebugConfiguration, token?: CancellationToken): ProviderResult<DebugConfiguration> {
    // if launch.json is missing or empty
    if (!config.type && !config.request && !config.name) {
      const editor = vscode.window.activeTextEditor
      if (editor && editor.document.languageId === 'koka') {
        config.type = 'koka'
        config.name = 'Launch'
        config.request = 'launch'
        config.program = '${file}'
        config.stopOnEntry = true
      }
    }

    if (!config.program) {
      return vscode.window.showInformationMessage("Cannot find a program to debug").then(_ => {
        return undefined	// abort launch
      })
    }

    return config
  }
}

class InlineDebugAdapterFactory implements vscode.DebugAdapterDescriptorFactory {

  constructor(private readonly config: KokaConfig) { }

  createDebugAdapterDescriptor(_session: vscode.DebugSession): ProviderResult<vscode.DebugAdapterDescriptor> {
    if (languageServer.languageClient)
      return new vscode.DebugAdapterInlineImplementation(new KokaDebugSession(this.config, languageServer.languageClient))
  }
}


class MainCodeLensProvider implements vscode.CodeLensProvider {
  private onDidChangeCodeLensesEmitter: EventEmitter<void> = new EventEmitter<void>()

  constructor(private readonly config: KokaConfig) { }

  public async provideCodeLenses(document: TextDocument, token: CancellationToken): Promise<CodeLens[] | undefined> {
    const doc = document.getText()
    const main = doc.indexOf('\nfun main')
    if (main < 0) {
      if (doc.startsWith('fun main')) {
        return [this.createCodeLens(document, 0)]
      }
      return []
    }
    return [this.createCodeLens(document, main + 1)]
  }

  private createCodeLens(document: TextDocument, offset: number): CodeLens {
    return new CodeLens(
      toRange(document, offset, 'main'.length),
      {
        arguments: [document.uri],
        command: "koka.startWithoutDebugging",
        title: `Run ${path.relative(this.config.cwd, document.uri.path)}`,
      }
    )
  }

}

function toRange(document: TextDocument, offset: number, length: number): vscode.Range {
  return new vscode.Range(document.positionAt(offset), document.positionAt(offset + length))
}