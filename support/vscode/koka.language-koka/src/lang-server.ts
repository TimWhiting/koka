/*---------------------------------------------------------------------------
Copyright 2023, Tim Whiting, Fredrik Wieczerkowski

This is free software; you can redistribute it and/or modify it under the
terms of the Apache License, Version 2.0. A copy of the License can be
found in the LICENSE file at the root of this distribution.
---------------------------------------------------------------------------*/

import * as vscode from "vscode"
import * as child_process from "child_process"

import {
  DidChangeConfigurationNotification,
  LanguageClient,
  LanguageClientOptions,
  RevealOutputChannelOn,
  ServerOptions,
} from 'vscode-languageclient/node'
import { KokaConfig } from "./workspace"

let stderrOutputChannel: vscode.OutputChannel
let firstRun = true

export class KokaLanguageServer {
  languageClient?: LanguageClient
  languageServerProcess?: child_process.ChildProcess
  outputChannel?: vscode.OutputChannel
  traceOutputChannel?: vscode.OutputChannel
  lspWriteEmitter: vscode.EventEmitter<string> = new vscode.EventEmitter<string>();
  lspPty?: vscode.Pseudoterminal
  lspTerminal?: vscode.Terminal

  constructor(context: vscode.ExtensionContext) {
    if (firstRun) {
      stderrOutputChannel = vscode.window.createOutputChannel('Koka Language Server Stderr')      
      context.subscriptions.push(stderrOutputChannel)
      firstRun = false;
    }
  }

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
    console.log(`Koka: Language Server: ${config.compilerPath} ${config.languageServerArgs.join(" ")}, Workspace: ${config.cwd}`)
    const serverOptions: ServerOptions = 
      {
        command: config.compilerPath,
        args: [...config.languageServerArgs, '--lsstdio'],
        options: { cwd: config.cwd, env: process.env }
      }
    // This issue: https://github.com/microsoft/vscode/issues/571
    // This sample: https://github.com/ShMcK/vscode-pseudoterminal/blob/master/src/extension.ts
    const formatText = (text: string) => `\r${text.split(/(\r?\n)/g).join("\r")}\r`;

    this.lspPty = {
      onDidWrite: (listener) => this.lspWriteEmitter.event((e) => listener(formatText(e))),
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
        if (config.autoFocusTerminal) {
          if (value.match(/error/gi)) {
            this.lspTerminal?.show(true)
          }
        }
      },
      clear: () => {
        this.lspWriteEmitter.fire("\x1b[2J\x1b[3J\x1b[;H")
      },
      show: () => this.lspTerminal?.show(true),
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
      revealOutputChannelOn: RevealOutputChannelOn.Info,
      traceOutputChannel: stderrOutputChannel,
      markdown: {
        isTrusted: true,
        supportHtml: true,
      },
      middleware: {
        executeCommand: async (command, args, next) => {
          console.log("intercepted command", command, args)
          if (command == "koka/signature-help/set-context") {
            // Trigger the signature help but with some context set on the backend
            console.log("Sending set-context request to server")
            next(command, args)
            console.log("Asking VSCode to trigger parameter hints")
            vscode.commands.executeCommand("editor.action.triggerParameterHints")
          } else {
            next(command, args)
          }
        }
      }
    }
    this.languageClient = new LanguageClient(
      'koka',
      "Koka Language Server Client",
      serverOptions,
      clientOptions
    )
    context.subscriptions.push(this)

    await this.languageClient.start()
    this.onConfigChanged(config)
    return this.languageClient
  }

  onConfigChanged(config: KokaConfig) {
    let isDark = vscode.window.activeColorTheme.kind == vscode.ColorThemeKind.Dark
    this.languageClient.sendNotification(DidChangeConfigurationNotification.type, {
      settings:
      {
        colors: { mode: isDark ? "dark" : "light" },
        inlayHints: {
          showImplicitArguments: config.showImplicitArguments,
          showInferredTypes: config.showInferredTypes,
          showFullQualifiers: config.showFullQualifiers,
        }

      }
    })
  }


  async dispose() {
    try {
      this.traceOutputChannel?.dispose()
      this.outputChannel?.dispose()
      await this.languageClient?.stop()
      await this.languageClient?.dispose()
      const result = this.languageServerProcess?.kill('SIGINT')
      if (!result) {
        console.log("Failed to end language server with SIGINT, trying SIGTERM")
        this.languageServerProcess?.kill()
      }
      // TODO: Does the terminal need to be disposed or is that handled by disposing the client
    } catch {
      // Ignore for now, the process should automatically die when the server / client closes the connection
    }
  }
}