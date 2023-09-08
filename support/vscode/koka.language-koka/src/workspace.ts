import * as path from "path"
import * as fs from "fs"
import * as vs from "vscode"
import * as os from "os"
import * as vscode from "vscode"
import * as child_process from "child_process"

interface SDKs { sdkPath: string, allSDKs: string[] }
const kokaExeName = os.platform() === "win32" ? "koka.exe" : "koka"

export function scanForSDK(): SDKs | undefined {
  const processPath = (process.env.PATH as string) || ""
  const paths = processPath.split(path.delimiter).filter((p) => p)

  const dev = path.join(process.env.HOME!, 'koka')
  let defaultSDK = ""
  let allSDKs = []
  if (fs.existsSync(dev)) {

    let command = 'stack path --local-install-root'
    const ghc = `${process.env.HOME}/.ghcup/env`
    if (fs.existsSync(ghc)) {
      // Linux ghcup installation does not show up in vscode's process.PATH, 
      // ensure stack uses the correct ghc by sourcing the ghcup env script 
      command = `${process.env.SHELL} -c "source ${ghc} && stack path --local-install-root"`
    }

    const options = { cwd: dev, env: process.env }
    const result = child_process.execSync(command, options)
    const devPath = result.toString().trim();
    // Prioritize dev
    const sdkPath = path.join(devPath, 'bin', kokaExeName)
    if (fs.existsSync(sdkPath)) {
      vs.window.showInformationMessage("Koka dev SDK found!")
      console.log("Koka: Using dev build of koka at " + devPath)
      defaultSDK = sdkPath
      allSDKs.push(defaultSDK)
    } else {
      vs.window.showInformationMessage("Koka dev environment found, but no built SDK")
    }
  }

  const local = path.join(process.env.HOME as string, '.local/bin')
  for (const p of [local].concat(paths)) {
    if (fs.existsSync(path.join(p, kokaExeName))) {
      console.log("Koka: Found build of koka at " + p)
      const sdkPath = path.join(p, kokaExeName)
      allSDKs.push(sdkPath)
      if (defaultSDK === "") {
        vs.window.showInformationMessage(`Using Koka SDK at ${p}`)
        defaultSDK = sdkPath
      }
    }
  }
  if (defaultSDK === "") {
    console.log('Koka: No Koka SDK found')
    vs.window.showWarningMessage("Koka SDK not found on path or in ~/.local/bin")
  } else {
    return { sdkPath: defaultSDK, allSDKs: allSDKs }
  }
}

export class KokaConfig {
  constructor(config: vscode.WorkspaceConfiguration, sdkPath: string, allSDKs: string[]) {
    this.config = config
    this.debugExtension = config.get('debugExtension') as boolean
    this.defaultSDK = sdkPath
    this.sdkPath = sdkPath
    this.allSDKs = allSDKs
    this.cwd = config.get('languageServer.cwd') as string || vscode.workspace.workspaceFolders![0].uri.path
    this.langServerArgs = []
    this.additionalArgs = config.get('languageServer.additionalArgs') as string[] || []
    this.selectSDK(sdkPath)
    this.target = "C"
  }
  defaultSDK: string
  sdkPath: string
  allSDKs: string[]
  config: vscode.WorkspaceConfiguration
  debugExtension: boolean
  command?: string | null
  langServerArgs: string[]
  additionalArgs: string[]
  target: string
  cwd: string

  selectSDK(path: string) {
    if (!fs.existsSync(path)) {
      this.command = null
      return
    }
    this.command = this.config.get('languageServer.command') as string || `${this.sdkPath}`
    this.langServerArgs = ["--language-server", `-i${this.cwd}`, ...this.additionalArgs]
  }

  selectTarget(t: string) {
    if (!["C", "JS", "WASM", "C#"].includes(t)) {
      return
    }
    this.target = t
  }
}