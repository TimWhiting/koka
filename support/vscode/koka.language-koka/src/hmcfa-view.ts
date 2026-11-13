/*---------------------------------------------------------------------------
Interactive view of the results of the full HMCFA analysis.
See analysis/hmcfa-viewer.md in the compiler repository for the roadmap.
---------------------------------------------------------------------------*/
import * as vscode from 'vscode'

// The shape of the `koka/hmcfa` result (see Core.FlowAnalysis.Full.DMCFA.View in the compiler).
interface SourceRange { line: number, column: number, endLine: number, endColumn: number }   // 1-based, end inclusive
interface HmcfaReport { module: string, file: string, m: number, h: number, entryPoints: unknown[], candidates?: string[], selected?: string | null, error?: string }

// `entry` is the entry point to analyze: a top-level function without parameters, or "" for the default ones.
type RunAnalysis = (filePath: string, m: number, h: number, variant: string, entry: string) => Promise<HmcfaReport | undefined>

export class HmcfaView implements vscode.Disposable {
  private panel?: vscode.WebviewPanel
  private file?: vscode.Uri              // the file the panel shows results for
  private statusBar: vscode.StatusBarItem
  private highlight: vscode.TextEditorDecorationType
  private subscriptions: vscode.Disposable[] = []
  private run = 0                        // the latest analysis run: results of earlier runs are dropped
  private variant?: string               // the variant chosen in this session; kept even if the setting cannot be written
  private entries = new Map<string, string>()   // the entry point chosen for each file ("" or absent: the default ones)

  constructor(private readonly runAnalysis: RunAnalysis) {
    this.statusBar = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Right, 90)
    this.statusBar.command = 'koka.setHMCFASensitivity'
    this.statusBar.tooltip = 'HMCFA timestamps keep m call sites and h handler levels. Click to change.'
    this.highlight = vscode.window.createTextEditorDecorationType({
      backgroundColor: new vscode.ThemeColor('editor.findMatchHighlightBackground'),
      borderRadius: '2px',
    })
    this.subscriptions.push(
      this.statusBar, this.highlight,
      vscode.window.onDidChangeActiveTextEditor(() => this.updateStatusBar()),
      vscode.workspace.onDidChangeConfiguration(e => {
        if (e.affectsConfiguration('koka.analysis')) this.updateStatusBar()
      }),
    )
    this.updateStatusBar()
  }

  dispose() {
    this.panel?.dispose()
    this.subscriptions.forEach(s => s.dispose())
  }

  private get sensitivity(): { m: number, h: number, variant: string } {
    const analysis = vscode.workspace.getConfiguration('koka.analysis')
    return { m: analysis.get<number>('callSensitivity') ?? 0, h: analysis.get<number>('handlerSensitivity') ?? 1,
             variant: this.variant ?? analysis.get<string>('variant') ?? 'dmcfa' }
  }

  // Switch between the variants of the analysis, and re-run it if the view is open.
  async setVariant(variant: string) {
    this.variant = variant === 'dmcfar' ? 'dmcfar' : 'dmcfa'
    const analysis = vscode.workspace.getConfiguration('koka.analysis')
    const target = vscode.workspace.workspaceFolders ? vscode.ConfigurationTarget.Workspace : vscode.ConfigurationTarget.Global
    // VS Code only registers a new setting after the window reloads: until then, the choice lasts for this session
    try { await analysis.update('variant', this.variant, target) }
    catch (e) { console.log('Koka: could not save koka.analysis.variant: ' + e) }
    this.updateStatusBar()
    if (this.panel) await this.refresh()
  }

  private updateStatusBar() {
    const { m, h, variant } = this.sensitivity
    this.statusBar.text = `$(telescope) ${variant.toUpperCase()} m=${m} h=${h}`
    if (vscode.window.activeTextEditor?.document.languageId === 'koka' || this.panel) this.statusBar.show()
    else this.statusBar.hide()
  }

  // Change the sensitivity in the settings, and re-run the analysis if the view is open.
  async setSensitivity(m: number, h: number) {
    const analysis = vscode.workspace.getConfiguration('koka.analysis')
    const target = vscode.workspace.workspaceFolders ? vscode.ConfigurationTarget.Workspace : vscode.ConfigurationTarget.Global
    await analysis.update('callSensitivity', Math.max(0, m), target)
    await analysis.update('handlerSensitivity', Math.max(0, h), target)
    this.updateStatusBar()
    if (this.panel) await this.refresh()
  }

  // Ask for a sensitivity from the status bar.
  async pickSensitivity() {
    const { m, h, variant } = this.sensitivity
    const presets = [[0, 0], [1, 0], [1, 1], [2, 1], [1, 2], [2, 2], [3, 3]]
    const items: (vscode.QuickPickItem & { m?: number, h?: number, variant?: string })[] = presets.map(([pm, ph]) => ({
      label: `m=${pm} h=${ph}`,
      description: (pm === m && ph === h ? 'current' : '') + (pm === 0 && ph === 0 ? ' context-insensitive' : ''),
      m: pm, h: ph,
    }))
    items.push({ label: 'Custom…' })
    const other = variant === 'dmcfar' ? 'dmcfa' : 'dmcfar'
    items.push({ label: '', kind: vscode.QuickPickItemKind.Separator },
               { label: `Switch to ${other.toUpperCase()}`, description: other === 'dmcfar' ? 'DMCFA with rebinding' : 'without rebinding', variant: other })
    const picked = await vscode.window.showQuickPick(items, {
      title: `HMCFA sensitivity (${variant.toUpperCase()})`, placeHolder: 'm call sites and h handler levels kept in each timestamp',
    })
    if (!picked) return
    if (picked.variant) return this.setVariant(picked.variant)
    if (picked.m !== undefined && picked.h !== undefined) return this.setSensitivity(picked.m, picked.h)
    const text = await vscode.window.showInputBox({
      title: 'HMCFA sensitivity', prompt: 'm and h, separated by a space', value: `${m} ${h}`,
      validateInput: v => /^\s*\d+\s+\d+\s*$/.test(v) ? undefined : 'Enter two non-negative integers, for example: 2 1',
    })
    if (!text) return
    const [cm, ch] = text.trim().split(/\s+/).map(Number)
    return this.setSensitivity(cm, ch)
  }

  // Show the results for the active Koka file.
  async show(context: vscode.ExtensionContext) {
    const editor = vscode.window.activeTextEditor
    if (editor?.document.languageId === 'koka') this.file = editor.document.uri
    if (!this.file) {
      vscode.window.showErrorMessage('Open a Koka file to analyze.')
      return
    }
    if (!this.panel) {
      this.panel = vscode.window.createWebviewPanel('koka.hmcfa', 'HMCFA', { viewColumn: vscode.ViewColumn.Beside, preserveFocus: true },
        { enableScripts: true, retainContextWhenHidden: true })
      this.panel.webview.html = viewHtml(this.panel.webview)
      this.panel.onDidDispose(() => {
        this.panel = undefined
        vscode.window.visibleTextEditors.forEach(e => e.setDecorations(this.highlight, []))
        this.updateStatusBar()
      }, null, context.subscriptions)
      this.panel.webview.onDidReceiveMessage(msg => this.onMessage(msg), null, context.subscriptions)
    }
    else {
      this.panel.reveal(undefined, true)
    }
    this.updateStatusBar()
    await this.refresh()
  }

  private async refresh() {
    if (!this.panel || !this.file) return
    const { m, h, variant } = this.sensitivity
    this.panel.title = `HMCFA: ${this.file.path.split('/').pop()}`
    this.panel.webview.postMessage({ type: 'loading', m, h, variant })
    const run = ++this.run
    let report: HmcfaReport | undefined
    const start = Date.now()
    try {
      report = await this.runAnalysis(this.file.fsPath, m, h, variant, this.entries.get(this.file.toString()) ?? '')
    }
    catch (e) {
      report = { module: '', file: this.file.fsPath, m, h, entryPoints: [], error: String(e) }
    }
    if (!report) report = { module: '', file: this.file.fsPath, m, h, entryPoints: [], error: 'The Koka language server did not return a result.' }
    const showGenerated = vscode.workspace.getConfiguration('koka.analysis').get<boolean>('showGenerated') ?? false
    if (run !== this.run) return          // a later run (another sensitivity or variant) has started: its result wins
    const seconds = (Date.now() - start) / 1000      // the whole request: type checking, the analysis, and building the results
    this.panel?.webview.postMessage({ type: 'report', report, m, h, variant, showGenerated, seconds })
  }

  private async onMessage(msg: any) {
    try { await this.handle(msg) }
    catch (e) { vscode.window.showErrorMessage('Koka HMCFA view: ' + (e instanceof Error ? e.message : String(e))) }
  }

  private async handle(msg: any) {
    switch (msg?.type) {
      case 'sensitivity': return this.setSensitivity(Number(msg.m), Number(msg.h))
      case 'refresh': return this.refresh()
      case 'variant': return this.setVariant(String(msg.variant))
      case 'entry':
        if (this.file) this.entries.set(this.file.toString(), String(msg.entry ?? ''))
        return this.refresh()
      case 'reveal': return this.reveal(msg.range as SourceRange)
    }
  }

  // Select and highlight a source range in the analyzed file.
  private async reveal(r: SourceRange) {
    if (!this.file || !r) return
    const range = new vscode.Range(r.line - 1, r.column - 1, r.endLine - 1, r.endColumn)
    const open = vscode.window.visibleTextEditors.find(e => e.document.uri.toString() === this.file!.toString())
    const editor = open ?? await vscode.window.showTextDocument(this.file, { viewColumn: vscode.ViewColumn.One, preserveFocus: true })
    editor.revealRange(range, vscode.TextEditorRevealType.InCenterIfOutsideViewport)
    editor.selection = new vscode.Selection(range.start, range.end)
    editor.setDecorations(this.highlight, [range])
  }
}

function nonce(): string {
  let text = ''
  const chars = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789'
  for (let i = 0; i < 32; i++) text += chars.charAt(Math.floor(Math.random() * chars.length))
  return text
}

function viewHtml(webview: vscode.Webview): string {
  const n = nonce()
  return /* html */`<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta http-equiv="Content-Security-Policy" content="default-src 'none'; style-src ${webview.cspSource} 'nonce-${n}'; script-src 'nonce-${n}';">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>HMCFA</title>
<style nonce="${n}">
  body { padding: 0 0 2em 0; font-family: var(--vscode-font-family); font-size: var(--vscode-font-size); color: var(--vscode-foreground); }
  code, .code { font-family: var(--vscode-editor-font-family); font-size: var(--vscode-editor-font-size); }
  .bar { position: sticky; top: 0; z-index: 2; display: flex; flex-wrap: wrap; gap: 6px 16px; align-items: center;
         padding: 8px 14px; background: var(--vscode-editor-background); border-bottom: 1px solid var(--vscode-panel-border); }
  .bar label { display: inline-flex; align-items: center; gap: 6px; white-space: nowrap; }
  .stepper { display: inline-flex; align-items: center; border: 1px solid var(--vscode-input-border, var(--vscode-panel-border)); border-radius: 3px; overflow: hidden; }
  .stepper button { border: 0; border-radius: 0; padding: 1px 8px; }
  .stepper span { min-width: 1.6em; text-align: center; font-variant-numeric: tabular-nums; }
  select { color: var(--vscode-dropdown-foreground); background: var(--vscode-dropdown-background); border: 1px solid var(--vscode-dropdown-border, transparent); border-radius: 3px; font: inherit; padding: 1px 4px; }
  button { color: var(--vscode-button-secondaryForeground); background: var(--vscode-button-secondaryBackground); border: 0; border-radius: 3px; padding: 2px 9px; cursor: pointer; font: inherit; }
  button:hover { background: var(--vscode-button-secondaryHoverBackground); }
  input[type=text] { color: var(--vscode-input-foreground); background: var(--vscode-input-background); border: 1px solid var(--vscode-input-border, transparent); border-radius: 3px; padding: 2px 6px; font: inherit; width: 11em; }
  .tabs { display: inline-flex; gap: 2px; }
  .tabs button.on { color: var(--vscode-button-foreground); background: var(--vscode-button-background); }
  main { padding: 4px 14px; }
  h2 { font-size: 1.05em; margin: 14px 0 6px 0; font-weight: 600; }
  .note { color: var(--vscode-descriptionForeground); margin: 8px 0; }
  .error { color: var(--vscode-errorForeground); white-space: pre-wrap; margin: 12px 0; }
  .entry { border-top: 1px solid var(--vscode-panel-border); padding: 7px 0 5px 0; }
  .entry.generated .src { opacity: 0.75; }
  .head { display: flex; gap: 10px; align-items: baseline; cursor: pointer; }
  .head:hover .src { text-decoration: underline; text-decoration-color: var(--vscode-descriptionForeground); }
  .pos { color: var(--vscode-descriptionForeground); font-variant-numeric: tabular-nums; min-width: 3.4em; text-align: right; flex: none; }
  .tag { color: var(--vscode-descriptionForeground); font-size: 0.85em; border: 1px solid var(--vscode-panel-border); border-radius: 3px; padding: 0 4px; flex: none; }
  .core { color: var(--vscode-descriptionForeground); font-size: 0.9em; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
  .results { margin: 4px 0 0 calc(3.4em + 10px); display: grid; grid-template-columns: max-content auto; gap: 5px 12px; align-items: center; }
  .values { display: flex; flex-wrap: wrap; gap: 4px; align-items: center; }
  .value { border-radius: 3px; padding: 0 5px; background: var(--vscode-textCodeBlock-background); }
  .value.any, .value.continuation { font-style: italic; }
  .kont { display: inline-block; vertical-align: top; }
  .kont > summary { cursor: pointer; list-style: none; }
  .kont > summary::before { content: '▸ '; color: var(--vscode-descriptionForeground); }
  .kont[open] > summary::before { content: '▾ '; }
  .kont[open] { display: block; margin: 2px 0 4px 0; }
  .kprog { margin: 3px 0 6px 14px; border-left: 3px solid var(--vscode-charts-blue); padding: 2px 0 2px 8px; }
  .ksrc { font-family: var(--vscode-editor-font-family); white-space: pre; }
  .khole { color: var(--vscode-charts-orange); font-weight: 700; }
  .kdelim { color: var(--vscode-charts-purple); font-style: italic; }
  .kref { color: var(--vscode-charts-orange); font-weight: 700; font-style: italic; }
  .kfrom { display: flex; flex-wrap: wrap; gap: 4px; align-items: baseline; margin-top: 3px; font-size: 0.9em; }
  .kpath { margin-top: 4px; }
  .performs { color: var(--vscode-descriptionForeground); }
  .arrow { color: var(--vscode-descriptionForeground); margin-right: 2px; }
  /* A timestamp: the stack from the outside in. Chips are call sites; a gate marks entering a handler or resuming. */
  .time { display: inline-flex; align-items: center; flex-wrap: wrap; gap: 3px; }
  .time > .site + .site::before, .time > .start + .site::before { content: "›"; color: var(--vscode-descriptionForeground); margin-right: 3px; }
  .site { border-radius: 3px; padding: 0 4px; white-space: nowrap; border: 1px solid color-mix(in srgb, var(--vscode-charts-blue) 45%, transparent); background: color-mix(in srgb, var(--vscode-charts-blue) 9%, transparent); }
  .site.link, .gate.link { cursor: pointer; }
  .site.link:hover, .gate.link:hover { outline: 1px solid var(--vscode-focusBorder); }
  .ln { color: var(--vscode-descriptionForeground); font-size: 0.82em; margin-left: 3px; }
  .gen { color: var(--vscode-descriptionForeground); cursor: help; }
  .start { color: var(--vscode-descriptionForeground); font-size: 0.9em; }
  .gate { white-space: nowrap; padding: 0 7px 0 9px; margin: 0 2px; border-radius: 0 9px 9px 0; border-left: 3px solid var(--vscode-charts-purple);
          background: color-mix(in srgb, var(--vscode-charts-purple) 16%, transparent); }
  .gate.local { border-left-color: var(--vscode-charts-green); background: color-mix(in srgb, var(--vscode-charts-green) 14%, transparent); }
  .gate.resume { border-left-color: var(--vscode-charts-orange); background: color-mix(in srgb, var(--vscode-charts-orange) 16%, transparent); }
  .gate .what { font-size: 0.82em; color: var(--vscode-descriptionForeground); }
  .gate .eff { font-family: var(--vscode-editor-font-family); font-weight: 600; }
  .legend { display: flex; flex-wrap: wrap; gap: 4px 14px; align-items: center; color: var(--vscode-descriptionForeground); font-size: 0.9em; margin: 8px 0 2px 0; }
  .legend > span { display: inline-flex; align-items: center; gap: 5px; }
  .empty { color: var(--vscode-descriptionForeground); font-style: italic; }
  /* The call stack view: nested frames from the outside in, each with what was evaluated in it. */
  .frame { margin-left: 14px; border-left: 1px solid var(--vscode-tree-indentGuidesStroke, var(--vscode-panel-border)); padding-left: 6px; }
  main > .frame { margin-left: 0; }
  .frame > summary { cursor: pointer; padding: 2px 0; display: list-item; }
  .frame > summary > * { vertical-align: baseline; }
  .joined { color: var(--vscode-charts-yellow); font-size: 0.8em; margin-left: 6px; cursor: help; }
  .count { color: var(--vscode-descriptionForeground); font-size: 0.8em; margin-left: 8px; font-variant-numeric: tabular-nums; }
  .here { display: grid; grid-template-columns: max-content max-content auto; gap: 3px 10px; align-items: center; margin: 3px 0 6px 18px; }
  .here .src { cursor: pointer; }
  .here .src:hover { text-decoration: underline; text-decoration-color: var(--vscode-descriptionForeground); }
  .k { color: var(--vscode-symbolIcon-keywordForeground, var(--vscode-debugTokenExpression-name)); }
  .n { color: var(--vscode-debugTokenExpression-number); }
  .s { color: var(--vscode-debugTokenExpression-string); }
  .c { color: var(--vscode-descriptionForeground); font-style: italic; }
  .t { color: var(--vscode-symbolIcon-classForeground, var(--vscode-debugTokenExpression-name)); }
</style>
</head>
<body>
<div class="bar">
  <label title="Number of call sites kept in a timestamp">call sites <b>m</b>
    <span class="stepper"><button id="m-down">−</button><span id="m">·</span><button id="m-up">+</button></span></label>
  <label title="Number of handler levels kept in a timestamp">handler levels <b>h</b>
    <span class="stepper"><button id="h-down">−</button><span id="h">·</span><button id="h-up">+</button></span></label>
  <label title="The entry point to analyze: any top-level function without parameters. By default, every function named analyze-…, or main when there are none.">entry
    <select id="entry"><option value="">default</option></select></label>
  <label title="The variant of the analysis: DMCFA, or DMCFAR (DMCFA with rebinding)">analysis
    <select id="variant"><option value="dmcfa">DMCFA</option><option value="dmcfar">DMCFAR</option></select></label>
  <span class="tabs" title="Cache: every expression and variable with its results at each timestamp. Call stack: the timestamps as nested frames, with what was evaluated in each."><button id="tab-cache" class="on">Cache</button><button id="tab-stack">Call stack</button></span>
  <label title="Show the results of expressions"><input type="checkbox" id="show-expression" checked> expressions</label>
  <label title="Show the values bound to variables"><input type="checkbox" id="show-binding" checked> bindings</label>
  <label title="Show expressions that are just a variable: bindings are immutable, so a variable has the value shown at its binding (variables bound by generated code, such as resume, are always shown)"><input type="checkbox" id="show-reference"> variable references</label>
  <label title="Show bindings and expressions whose only values are top-level functions (definitions and library functions)"><input type="checkbox" id="show-toplevel"> top-level functions</label>
  <input type="text" id="filter" placeholder="Filter by source text">
  <label><input type="checkbox" id="generated"> generated code</label>
  <button id="refresh">Re-run</button>
  <span id="status" class="note"></span>
</div>
<main id="main"></main>
<script nonce="${n}">
(function () {
  const vscode = acquireVsCodeApi()
  const state = { report: null, m: 0, h: 0, variant: 'dmcfa', view: 'cache', kinds: { expression: true, binding: true }, references: false, toplevel: false, filter: '', generated: false, seconds: 0 }
  const duration = t => t < 1 ? Math.round(t * 1000) + ' ms' : t.toFixed(t < 10 ? 2 : 1) + ' s'
  const $ = id => document.getElementById(id)
  const el = (tag, cls, text) => { const e = document.createElement(tag); if (cls) e.className = cls; if (text !== undefined) e.textContent = text; return e }

  // A small Koka highlighter: keywords, numbers, strings, comments and capitalized names.
  const keywords = new Set(('fun fn val var with ctl effect handler handle match if then else elif return in type struct alias import module pub ' +
    'extern abstract co rec open extend behind named linear raw final override mask forall exists some infix infixl infixr value reference div exn total').split(' '))
  const token = /(\\/\\/.*$)|("(?:[^"\\\\]|\\\\.)*"?)|('(?:[^'\\\\]|\\\\.)')|(\\b\\d[\\d_]*(?:\\.\\d+)?\\b)|([A-Za-z_@][\\w\\-@']*)/gm
  function highlight(text) {
    const span = el('span', 'code')
    let last = 0
    for (const match of text.matchAll(token)) {
      if (match.index > last) span.append(text.slice(last, match.index))
      const [all, comment, str, chr, num, word] = match
      const cls = comment ? 'c' : (str || chr) ? 's' : num ? 'n' : keywords.has(word) ? 'k' : /^[A-Z]/.test(word) ? 't' : null
      if (cls) span.append(el('span', cls, all)); else span.append(all)
      last = match.index + all.length
    }
    if (last < text.length) span.append(text.slice(last))
    return span
  }

  function reveal(range) { if (range) vscode.postMessage({ type: 'reveal', range }) }

  function site(s) {
    if (s.text.startsWith('generated: ')) {    // a call made by compiler-generated or library code
      const g = el('span', 'gen', '•'); g.title = 'A call made by compiler-generated or library code: ' + s.text.slice(11); return g
    }
    const e = el('span', 'site' + (s.range ? ' link' : ''))
    e.append(highlight(s.text))
    if (s.range) {
      e.append(el('span', 'ln', ':' + s.range.line))
      e.title = 'Go to line ' + s.range.line
      e.addEventListener('click', ev => { ev.preventDefault(); ev.stopPropagation(); reveal(s.range) })
    }
    return e
  }

  // The call sites of one segment of the stack, outermost first (the analysis keeps them innermost first).
  function segment(calls) {
    const frag = document.createDocumentFragment()
    for (const s of [...calls.sites].reverse()) {
      if (s.text === 'top') { const t = el('span', 'start', 'start'); t.title = 'The start of the program'; frag.append(t) }
      else if (s.text === 'handler') continue      // the stack restarts at a delimiter: the gate before it already says so
      else frag.append(site(s))
    }
    return frag
  }

  // A delimiter: entering a handler, or resuming a continuation.
  function gate(h) {
    const g = el('span', 'gate ' + h.kind)
    g.append(el('span', 'what', (h.kind === 'resume' ? 'resume into ' : h.kind === 'local' ? 'var ' : 'handle ')))
    g.append(el('span', 'eff', h.effect))
    if (h.at && h.at.range) {
      const where = el('span', 'ln', ':' + h.at.range.line + (h.others ? ' (+' + h.others + ')' : ''))
      g.append(where)
      g.classList.add('link')
      g.addEventListener('click', ev => { ev.preventDefault(); ev.stopPropagation(); reveal(h.at.range) })
    }
    g.title = h.kind === 'local'
      ? 'Inside the scope of the local variable ' + h.effect + ' (a var is a handler: reading and assigning it are operations). To the left: the calls outside it.'
      : h.kind === 'resume'
      ? 'A continuation captured by the ' + h.effect + ' handler was resumed here. To the left: the calls that led to the resume. To the right: calls made by the resumed code.'
      : 'The handler for ' + h.effect + ' was installed here' + (h.others ? ' (or at one of ' + h.others + ' other handlers for this effect)' : '') +
        '. To the left: the calls that led to installing it. To the right: calls made inside the handled code.'
    return g
  }

  // A timestamp is drawn as the stack from the outside in (left to right):
  // for each delimiter, the calls made before crossing it, then the delimiter; finally the calls made since the last one.
  function time(t) {
    const root = el('span', 'time')
    for (const h of [...t.handlers].reverse()) root.append(segment(h.calls), gate(h))
    if (!t.handlers.length && t.calls.inHandler) {
      const g = el('span', 'gate handle', 'handler'); g.title = 'Inside a handler (handler levels are not tracked: h = 0)'; root.append(g)
    }
    const inner = segment(t.calls)
    root.append(inner)
    if (!root.childNodes.length) root.append(el('span', 'empty', 'start'))
    return root
  }

  // An entry whose only values are top-level functions (a definition, or a library function such as println or +).
  function onlyTopLevel(e) {
    const vs = e.results.flatMap(r => r.values)
    return vs.length > 0 && vs.every(v => v.kind === 'function' && v.top)
  }

  // A continuation in its finite form, shown as source: what is left of each function the continuation returns
  // through, with the inner fragment plugged into the outer one's hole, so it reads as one program whose □ is the
  // value passed to resume. A frame that recurs in the continuation store (a cycle) is the only thing that needs
  // abstraction: it gets a name, K, defined once, and the name stands for it wherever the continuation comes back
  // to it. Where the analysis does not know which way the continuation goes, each way is shown.
  const HOLE = '□'
  function kontView(v) {
    const box = el('details', 'kont')
    const summary = el('summary', 'value continuation')
    summary.append(v.text)
    summary.title = 'Show what is left to run when resume is called, as source'
    box.append(summary)
    const k = v.kont
    if (!k) return box
    const byId = new Map(k.frames.map(f => [f.id, f]))
    const next = f => f.next.map(i => byId.get(i)).filter(Boolean)
    const start = byId.get(k.start)
    if (!start) return box
    // loop heads: frames a path comes back to (the targets of back edges in a depth-first walk)
    const heads = new Map(), onStack = new Set(), done = new Set()
    const dfs = f => {
      onStack.add(f.id)
      for (const n of next(f)) {
        if (onStack.has(n.id)) { if (!heads.has(n.id)) heads.set(n.id, null) }
        else if (!done.has(n.id)) dfs(n)
      }
      onStack.delete(f.id); done.add(f.id)
    }
    dfs(start)
    let count = 0
    for (const id of heads.keys()) heads.set(id, heads.size === 1 ? 'K' : 'K' + (++count))
    // the ways from a frame to the operation, stopping at a loop head (other than the one being defined)
    const MAX = 4
    const ways = from => {
      const out = []
      let more = 0
      const walk = (f, path) => {
        if (out.length >= MAX) { more++; return }
        if (path.length && heads.has(f.id)) { out.push({ frames: path, ref: heads.get(f.id) }); return }
        const p = [...path, f], ns = next(f)
        if (!ns.length) { out.push({ frames: p }); return }
        for (const n of ns) walk(n, p)
      }
      walk(from, [])
      return { list: dedupe(out.map(w => renderWay(w, k))), more }
    }
    const opText = k.opAt ? k.opAt.text : k.op
    box.append(el('div', 'note', HOLE + ' is the value passed to resume (what ' + opText + ' returns); the rest is what runs after it, until the ' + k.effect + ' handler gets the result.'))
    const show = (w, label) => {
      w.list.forEach((r, i) => {
        if (w.list.length > 1) box.append(el('div', 'note kpath', (i ? 'or ' : label) + (i + 1) + ' of ' + (w.list.length + w.more) + ':'))
        box.append(r)
      })
      if (w.more) box.append(el('div', 'note', w.more + ' more not shown.'))
    }
    // when the continuation starts in a loop, or its ways are exactly a loop's, it is just that loop's name
    const main = heads.has(start.id) ? null : ways(start)
    const same = main && [...heads].find(([id]) => { const w = ways(byId.get(id)); return w.list.length === main.list.length && w.list.every((b, i) => b.textContent === main.list[i].textContent) })
    if (!main || same) box.append(codeBlock([main ? same[1] : heads.get(start.id)], []))
    else show(main, 'way ')
    for (const [id, name] of heads) {
      box.append(el('div', 'note kpath', name + ' recurs (its first frame is in its own continuation), so ' + name + ' may appear inside ' + name + ' any number of times. ' + name + ' is:'))
      show(ways(byId.get(id)), name + ' ')
    }
    return box
  }

  function dedupe(blocks) {
    const seen = new Set()
    return blocks.filter(b => { const t = b.textContent; if (seen.has(t)) return false; seen.add(t); return true })
  }

  const within = (a, b) => // range b inside range a
    (a.line < b.line || (a.line === b.line && a.column <= b.column)) && (a.endLine > b.endLine || (a.endLine === b.endLine && a.endColumn >= b.endColumn))

  // The fragments of one way, outermost first: a function's remaining source, or a delimiter the value returns through.
  // Consecutive frames are one activation only when the inner one is inside the outer one's hole (a recursive call
  // of the same function is a new activation).
  function fragments(frames) {
    const out = []
    for (const f of frames) {
      if (f.act === undefined || f.act === null) {
        if (f.kind !== 'op') out.push({ delim: f.text, frames: [f] })
        continue
      }
      const last = out[out.length - 1]
      const lastF = last && last.frames[last.frames.length - 1]
      if (last && last.act === f.act && lastF.hole && within(lastF.hole, f.region || f.hole)) last.frames.push(f)
      else out.push({ act: f.act, frames: [f] })
    }
    return out
  }

  function renderWay(way, k) {
    const frags = fragments(way.frames)
    let text = [way.ref || HOLE]
    for (let i = frags.length - 1; i >= 0; i--) text = plug(fragmentLines(frags[i], k), text)
    return codeBlock(text, frags.filter(fr => !fr.delim).map(fr => ({ act: k.acts[fr.act], hole: fr.frames[fr.frames.length - 1].hole })))
  }

  function codeBlock(text, sources) {
    const box = el('div', 'kprog')
    const code = el('div', 'ksrc')
    for (const l of text) {
      const row = el('div', 'kline')
      for (const part of l.split(/(□|⟨[^⟩]*⟩|\bK\d*\b)/)) {
        if (part === HOLE) row.append(el('span', 'khole', HOLE))
        else if (part.startsWith('⟨')) row.append(el('span', 'kdelim', part))
        else if (/^K\d*$/.test(part)) row.append(el('span', 'kref', part))
        else if (part) row.append(highlight(part))
      }
      code.append(row)
    }
    box.append(code)
    if (sources.length) {
      const from = el('div', 'kfrom')
      from.append(el('span', 'note', 'from'))
      for (const { act, hole } of sources) {
        const s = el('span', 'site link', act.name)
        s.append(el('span', 'ln', ':' + hole.line))
        s.title = 'Go to the hole on line ' + hole.line
        s.addEventListener('click', ev => { ev.preventDefault(); ev.stopPropagation(); reveal(hole) })
        from.append(s)
      }
      box.append(from)
    }
    return box
  }

  // The source of one activation's fragment: its outermost frame's expression, with the innermost frame's hole as □.
  function fragmentLines(frag, k) {
    if (frag.delim) return ['⟨' + frag.delim + '⟩', '  ' + HOLE]
    const act = k.acts[frag.act]
    const outer = frag.frames[0], hole = frag.frames[frag.frames.length - 1].hole
    const region = outer.region || outer.hole
    // from the line of the first hole (what came before it has run), to the end of the outermost frame's expression
    const from = Math.min(...frag.frames.map(f => f.hole.line)), to = Math.max(region.endLine, hole.endLine)
    let lines = act.lines.slice(from - act.first, to - act.first + 1)
    // the first line starts where the outermost frame's expression does (kept as spaces, so columns stay put)
    if (region.line === from) lines[0] = ' '.repeat(region.column - 1) + lines[0].slice(region.column - 1)
    const last = to - from
    if (region.endLine === to && last >= 0) {
      // cut after the expression, but keep closing brackets that follow it on the line
      const cut = Math.max(region.endColumn, hole.line === to ? hole.endColumn : 0), rest = lines[last].slice(cut)
      if (!/^[\s)}\]]*$/.test(rest)) lines[last] = lines[last].slice(0, cut)
    }
    const a = hole.line - from, b = hole.endLine - from
    if (a >= 0 && b < lines.length) lines = [...lines.slice(0, a), lines[a].slice(0, hole.column - 1) + HOLE + lines[b].slice(hole.endColumn), ...lines.slice(b + 1)]
    return dedent(lines)
  }

  function dedent(lines) {
    const n = Math.min(...lines.filter(l => l.trim()).map(l => l.match(/^ */)[0].length))
    return lines.map(l => l.slice(n))
  }

  // Put inner where the □ of outer is: inline when it is one line, otherwise as an indented block.
  function plug(outer, inner) {
    const r = outer.findIndex(l => l.includes(HOLE))
    if (r < 0) return outer
    const line = outer[r], c = line.indexOf(HOLE)
    const before = line.slice(0, c), after = line.slice(c + 1)
    let mid
    if (inner.length === 1) {
      const t = inner[0], paren = after.trim() !== '' && / /.test(t) && t !== HOLE
      mid = [before + (paren ? '(' + t + ')' : t) + after]
    } else if (!before.trim() && !after.trim()) {
      mid = inner.map(l => before + l)
    } else {
      const ind = ' '.repeat(line.match(/^ */)[0].length + 2)
      mid = after.trim() ? [before + '(', ...inner.map(l => ind + l), ' '.repeat(ind.length - 2) + ')' + after] : [before.replace(/\s+$/, ''), ...inner.map(l => ind + l)]
    }
    return [...outer.slice(0, r), ...mid, ...outer.slice(r + 1)]
  }

  function values(result) {
    const box = el('div', 'values')
    box.append(el('span', 'arrow', '→'))
    for (const v of result.values) {
      if (v.kind === 'continuation') { box.append(kontView(v)); continue }
      const e = el('span', 'value ' + v.kind)
      if (v.kind === 'function' || v.kind === 'constructor' || v.kind === 'literal') e.append(highlight(v.text)); else e.textContent = v.text
      box.append(e)
    }
    for (const op of result.performs) box.append(el('span', 'performs', 'performs ' + op + ' (handled outside this expression)'))
    if (!result.values.length && !result.performs.length) box.append(el('span', 'empty', 'nothing'))
    return box
  }

  function entry(e) {
    const row = el('div', 'entry' + (e.generated ? ' generated' : ''))
    const head = el('div', 'head')
    head.title = 'Go to ' + e.range.line + ':' + e.range.column
    head.addEventListener('click', () => reveal(e.range))
    const src = el('span', 'src'); src.append(e.kind === 'binding' ? el('span', 'k', 'val ') : '', highlight(e.text))
    head.append(el('span', 'pos', e.range.line + ':' + e.range.column), src)
    if (e.generated) { head.append(el('span', 'tag', 'generated')); if (e.kind === 'expression') head.append(el('span', 'core code', e.core)) }
    row.append(head)
    const results = el('div', 'results')
    for (const r of e.results) results.append(time(r.time), values(r))
    row.append(results)
    return row
  }

  // The call stack view. A timestamp is a stack from the outside in (the same order as the timestamps in the other tabs), made of segments:
  // the call sites up to a delimiter (entering a handler, or resuming), then the delimiter; the last segment has no delimiter.
  // A segment is complete when it starts at the program start (the first segment) or at its delimiter (the others);
  // otherwise it was cut to its m newest calls.
  function segments(t) {
    const segs = []
    const seg = (calls, first, gate) => segs.push({
      sites: [...calls.sites].reverse().filter(s => s.text !== 'handler').map(s => ({
        key: s.text === 'top' ? 'start' : s.id ? 'call ' + s.id : 'site ' + s.text, range: s.range, id: s.id,
        node: () => s.text === 'top' ? el('span', 'start', 'start') : site(s) })),
      complete: calls.sites.some(s => s.text === (first ? 'top' : 'handler')),
      gate })
    for (const h of [...t.handlers].reverse())
      seg(h.calls, !segs.length, { key: 'gate ' + h.kind + ' ' + h.effect + (h.at && h.at.range ? '@' + h.at.range.line + ':' + h.at.range.column : ''), range: h.at && h.at.range, node: () => gate(h) })
    if (!t.handlers.length && t.calls.inHandler)    // handler levels are not tracked (h = 0): the stack outside is unknown
      segs.push({ sites: [], complete: false, gate: { key: 'gate handler', node: () => { const g = el('span', 'gate handle', 'handler'); g.title = 'Inside a handler (handler levels are not tracked: h = 0)'; return g } } })
    seg(t.calls, !segs.length, null)
    return segs
  }

  // The tree mirrors the call stack: a frame's children are the calls made from it, and each frame lists what was bound
  // and evaluated in exactly that context. A complete segment goes in as it is. A cut segment continues the context its
  // oldest kept call was made in: a context (inside the same delimiter) that ends with the calls before it and that
  // evaluated that call. With truncated timestamps such contexts can form cycles (recursion, repeated resumes), so each
  // cut segment is placed once, below the shallowest such context. When there is none, a cut first segment goes below
  // a frame that says the older calls were not kept, and a cut inner segment goes right below its delimiter.
  // The tree is built from the timestamps of all entries (hidden ones connect the others), and shows the results of the shown entries.
  const rangeKey = r => r.line + ':' + r.column + '-' + r.endLine + ':' + r.endColumn
  function stackTree(entries, contexts, shown) {
    const newNode = (parent, f) => ({ key: parent ? parent.key + '/' + f.key : '', frame: f, parent, children: new Map(), here: [], end: false, evals: new Set(), joined: 0, count: 0 })
    const root = newNode(null, null)
    const lost = newNode(root, { key: 'lost', node: () => { const s = el('span', 'start', '… older calls not kept'); s.title = 'These stacks are deeper than the timestamps keep (m = ' + state.m + ', h = ' + state.h + '), and no context they continue was found'; return s } })
    root.children.set('lost', lost)
    const insert = (node, frames) => {
      for (const f of frames) {
        if (!node.children.has(f.key)) node.children.set(f.key, newNode(node, f))
        node = node.children.get(f.key)
      }
      return node
    }
    const byTime = new Map()
    const at = time => {
      if (!byTime.has(time.key)) byTime.set(time.key, { segs: segments(time), results: [], evals: new Set() })
      return byTime.get(time.key)
    }
    for (const e of entries) for (const r of e.results) {
      const t = at(r.time)
      if (shown.has(e)) t.results.push({ e, r })
      if (e.kind === 'expression') t.evals.add(e.id)
    }
    // every timestamp something was evaluated at (also in library code), with what was evaluated: these connect the stacks
    for (const c of contexts) { const t = at(c.time); for (const id of c.evals) t.evals.add(id) }
    const overlap = state.m - 1
    const endsWith = (node, keys) => {
      let n = node
      for (let i = keys.length - 1; i >= 0; i--, n = n.parent) if (!n || n === root || n.frame.key !== keys[i]) return false
      return true
    }
    // the contexts at and below a frame, breadth first so the shallowest comes first; not past another delimiter
    const below = scope => {
      const out = [], queue = scope === root ? [...scope.children.values()] : [scope]
      while (queue.length) {
        const n = queue.shift()
        if (n.end) out.push(n)
        if (n === scope || !n.frame.key.startsWith('gate ')) queue.push(...n.children.values())
      }
      return out
    }
    // place one segment below node (the root or a delimiter); undefined when it has to wait for its context
    const place = (node, s, first, force) => {
      if (s.complete) return insert(first ? root : node, s.sites)
      const keys = s.sites.slice(0, overlap).map(f => f.key)
      const call = s.sites[overlap] && s.sites[overlap].id        // the newest call, by its expression
      const hosts = s.sites.length >= state.m && (overlap >= 1 || call)
        ? below(first ? root : node).filter(n => endsWith(n, keys) && (!call || n.evals.has(call))) : []
      if (!hosts.length) return force ? insert(first ? lost : node, s.sites) : undefined
      const host = hosts[0]
      const joint = s.sites[overlap] ? host.children.has(s.sites[overlap].key) : true
      const end = insert(host, s.sites.slice(overlap))
      if (!joint) host.children.get(s.sites[overlap].key).joined = hosts.length - 1
      return end
    }
    let pending = [...byTime.values()].map(t => ({ t, node: root, i: 0 }))
    const advance = (p, force) => {
      let moved = false
      for (const segs = p.t.segs; p.i < segs.length; p.i++, force = false, moved = true) {
        const s = segs[p.i]
        const node = place(p.node, s, p.i === 0, force)
        if (!node) return moved
        p.node = s.gate ? insert(node, [s.gate]) : node
      }
      p.node.end = true
      p.node.here.push(...p.t.results)
      p.t.evals.forEach(r => p.node.evals.add(r))
      return true
    }
    const waitingOn = p => { const s = p.t.segs[p.i]; return s.sites[overlap] && s.sites[overlap].id }
    while (pending.length) {
      let changed = false
      for (const p of pending) changed = advance(p, false) || changed
      pending = pending.filter(p => p.i < p.t.segs.length)
      if (changed || !pending.length) continue
      // nothing could be placed: place one segment without its context, which may let the others continue. Prefer one
      // that can never be matched: its call is not in the source, or no waiting timestamp evaluates it (a captured stack).
      const later = p => { const call = waitingOn(p); return call && pending.some(q => q.t.evals.has(call)) }
      const p = pending.find(p => !waitingOn(p)) ?? pending.find(p => !later(p)) ?? pending[0]
      advance(p, true)
      pending = pending.filter(p => p.i < p.t.segs.length)
    }
    root.children.delete('lost'); root.children.set('lost', lost)      // after the stacks that start at the program start
    const count = n => (n.count = n.here.length + [...n.children.values()].reduce((s, c) => s + count(c), 0))
    count(root)
    const prune = n => { for (const [k, c] of n.children) { if (!c.count) n.children.delete(k); else prune(c) } }
    prune(root)
    return root
  }

  // Frames the user opened or closed, by path; frames start open down to a few levels.
  const opened = new Map()
  let openAll = false
  function frameView(node, depth) {
    const box = el('details', 'frame')
    box.open = opened.has(node.key) ? opened.get(node.key) : (openAll || depth < 3 || node.children.size === 1)
    box.addEventListener('toggle', () => opened.set(node.key, box.open))
    const summary = el('summary')
    summary.append(node.frame.node(), el('span', 'count', String(node.count)))
    summary.title = node.count + ' result' + (node.count === 1 ? '' : 's') + ' in this context and the calls it makes'
    if (node.joined) {
      const j = el('span', 'joined', '+' + node.joined)
      j.title = 'This call could also have been made from ' + node.joined + ' other context' + (node.joined === 1 ? '' : 's') +
        ' with the same newest calls: the timestamps keep only m = ' + state.m + ' calls, so they cannot tell these apart'
      summary.append(j)
    }
    box.append(summary)
    box.append(...frameBody(node, depth + 1))
    return box
  }

  // What was evaluated in a frame, with the frames of the calls it made in between: a call's frame comes right after
  // the row of the call expression (or of the with / resume for a delimiter). Frames of calls that are not in the source last.
  function frameBody(node, depth) {
    const rows = hereRows(node.here)
    const items = [...rows.map(r => ({ range: r.range, row: r })),
                   ...[...node.children.values()].map(c => ({ range: c.frame.range, child: c }))]
    const order = (a, b) => {
      if (!a.range || !b.range) return (a.range ? 0 : 1) - (b.range ? 0 : 1)
      return a.range.line - b.range.line || a.range.endLine - b.range.endLine || a.range.endColumn - b.range.endColumn ||
             b.range.column - a.range.column || (a.row ? 0 : 1) - (b.row ? 0 : 1)
    }
    items.sort(order)
    const out = []
    let list = null
    for (const it of items) {
      if (it.row) {
        if (!list) { list = el('div', 'here'); out.push(list) }
        list.append(...it.row.cells)
      }
      else { list = null; out.push(frameView(it.child, depth)) }
    }
    return out
  }

  // What was bound (variables) and evaluated (expressions) in one context: one row per source expression, with its cells.
  function hereRows(here) {
    // One row per source expression: results for the same range and text (the same expression at timestamps that
    // land on this frame, or a variable and its binding) are joined. A row is a binding if any of its results is.
    const rows = new Map()
    for (const { e, r } of here) {
      const key = rangeKey(e.range) + ' ' + e.text
      if (!rows.has(key)) rows.set(key, { e, binding: false, values: [], performs: [] })
      const row = rows.get(key)
      row.binding = row.binding || e.kind === 'binding'
      for (const v of r.values) if (!row.values.some(w => w.kind === v.kind && w.text === v.text)) row.values.push(v)
      for (const op of r.performs) if (!row.performs.includes(op)) row.performs.push(op)
    }
    // in evaluation order: by line, then by where the expression ends (parts before the whole), then by where it starts
    const sorted = [...rows.values()].sort(({ e: a }, { e: b }) =>
      a.range.line - b.range.line || a.range.endLine - b.range.endLine || a.range.endColumn - b.range.endColumn || b.range.column - a.range.column)
    return sorted.map(({ e, binding, values: vs, performs }) => {
      const src = el('span', 'src link')
      src.append(binding ? el('span', 'k', 'val ') : '', highlight(e.text))
      src.title = 'Go to ' + e.range.line + ':' + e.range.column
      src.addEventListener('click', () => reveal(e.range))
      return { range: e.range, cells: [el('span', 'pos', e.range.line + ':' + e.range.column), src, values({ values: vs, performs })] }
    })
  }

  function render() {
    $('m').textContent = state.m; $('h').textContent = state.h; $('variant').value = state.variant
    $('generated').checked = state.generated
    $('tab-cache').className = state.view === 'cache' ? 'on' : ''
    $('tab-stack').className = state.view === 'stack' ? 'on' : ''
    $('show-expression').checked = state.kinds.expression; $('show-binding').checked = state.kinds.binding
    $('show-reference').checked = state.references; $('show-toplevel').checked = state.toplevel
    const main = $('main'); const report = state.report
    if (!report) return
    main.replaceChildren()
    if (report.error) { main.append(el('div', 'error', report.error)); return }
    if (!report.entryPoints.length) {
      main.append(el('p', 'note', 'No entry point found: add a main function or a function named analyze-….'))
      return
    }
    const legend = el('div', 'legend')
    const item = (node, text) => { const i = el('span'); i.append(node, text); return i }
    legend.append('A timestamp reads from the outside in:',
      item(el('span', 'site', 'f(x)'), 'a call site we are inside'),
      item(el('span', 'gate handle', 'handle eff'), 'entered a handler: calls after it are inside the handled code'),
      item(el('span', 'gate resume', 'resume into eff'), 'resumed a continuation: calls after it belong to the resumed code'),
      item(el('span', 'gate local', 'var x'), 'inside the scope of a local variable'))
    main.append(legend)
    const needle = state.filter.trim().toLowerCase()
    for (const ep of report.entryPoints) {
      const title = el('h2'); title.append('Entry point ', highlight(ep.name)); main.append(title)
      if (ep.timedOut) { main.append(el('p', 'note', 'The analysis did not finish within 60 seconds.')); continue }
      // a reference is left out only when its variable has a binding in the source that shows the value instead
      const declared = new Set(ep.entries.filter(e => e.kind === 'binding' && !e.generated).map(e => e.text))
      const all = ep.entries.filter(e => state.kinds[e.kind] && (state.references || !(e.reference && declared.has(e.text))) && (state.toplevel || !onlyTopLevel(e)))
      const shown = all.filter(e => (state.generated || !e.generated) && (!needle || e.text.toLowerCase().includes(needle)))
      // by line, then where it ends (parts before the whole), then where it starts
      shown.sort((a, b) => a.range.line - b.range.line || a.range.endLine - b.range.endLine || a.range.endColumn - b.range.endColumn || b.range.column - a.range.column)
      const hidden = all.filter(e => e.generated).length
      const what = state.kinds.expression && state.kinds.binding ? 'expressions and bindings' : state.kinds.expression ? 'expressions' : state.kinds.binding ? 'bindings' : 'entries'
      const timing = el('p', 'note timing')
      if (ep.seconds !== undefined) timing.append(el('b', '', 'Analyzed in ' + duration(ep.seconds)))   // older compilers do not say
      timing.append((ep.seconds !== undefined ? ' with ' : 'With ') + state.variant.toUpperCase() + ' at m = ' + state.m + ', h = ' + state.h + ': ' + ep.cacheSize + ' entries in the analysis cache. ' +
        'The whole request took ' + duration(state.seconds) + ', including type checking and building these results.')
      timing.title = 'Analyzed in: the fixpoint iteration of the abstract interpreter for this entry point'
      main.append(timing)
      main.append(el('p', 'note', shown.length + ' ' + what + ' shown' +
        (!state.generated && hidden ? ', ' + hidden + ' generated hidden' : '') + '.'))
      if (state.view !== 'stack') { for (const e of shown) main.append(entry(e)); continue }
      main.append(el('p', 'note', state.m > 0
        ? 'Each segment of a stack keeps only its ' + state.m + ' newest call' + (state.m === 1 ? '' : 's') + ' (m = ' + state.m + '), so a stack starts at the oldest call kept: ' +
          'it starts at the program start only when the whole stack fits.'
        : 'Call sites are not tracked (m = 0): frames are only handlers and resumptions.'))
      const tree = stackTree(ep.entries, ep.contexts ?? [], new Set(shown))
      let size = 0; const sizeOf = n => { size++; n.children.forEach(sizeOf) }; sizeOf(tree)
      openAll = size <= 80
      main.append(...frameBody(tree, 0))
    }
  }

  // update the shown values right away, so quick presses add up
  const step = (dm, dh) => {
    state.m = Math.max(0, state.m + dm); state.h = Math.max(0, state.h + dh)
    $('m').textContent = state.m; $('h').textContent = state.h
    vscode.postMessage({ type: 'sensitivity', m: state.m, h: state.h })
  }
  $('m-down').addEventListener('click', () => step(-1, 0)); $('m-up').addEventListener('click', () => step(1, 0))
  $('h-down').addEventListener('click', () => step(0, -1)); $('h-up').addEventListener('click', () => step(0, 1))
  $('tab-cache').addEventListener('click', () => { state.view = 'cache'; render() })
  $('tab-stack').addEventListener('click', () => { state.view = 'stack'; render() })
  $('show-expression').addEventListener('change', ev => { state.kinds.expression = ev.target.checked; render() })
  $('show-binding').addEventListener('change', ev => { state.kinds.binding = ev.target.checked; render() })
  $('show-reference').addEventListener('change', ev => { state.references = ev.target.checked; render() })
  $('show-toplevel').addEventListener('change', ev => { state.toplevel = ev.target.checked; render() })
  $('filter').addEventListener('input', ev => { state.filter = ev.target.value; render() })
  $('generated').addEventListener('change', ev => { state.generated = ev.target.checked; render() })
  $('refresh').addEventListener('click', () => vscode.postMessage({ type: 'refresh' }))
  $('variant').addEventListener('change', ev => vscode.postMessage({ type: 'variant', variant: ev.target.value }))
  $('entry').addEventListener('change', ev => vscode.postMessage({ type: 'entry', entry: ev.target.value }))
  // The entry point choices come with each report: the module's top-level functions without parameters.
  function updateEntries(report) {
    const sel = $('entry'), names = report.candidates || []
    const isDefault = n => n.startsWith('analyze-') || (n === 'main' && !names.some(x => x.startsWith('analyze-')))
    sel.replaceChildren(el('option', null, 'default (' + (names.filter(isDefault).join(', ') || 'none') + ')'))
    sel.firstChild.value = ''
    for (const n of names) { const o = el('option', null, n); o.value = n; sel.append(o) }
    sel.value = report.selected || ''
  }

  let first = true
  let timer
  window.addEventListener('message', ev => {
    const msg = ev.data
    if (msg.type === 'loading') {
      state.m = msg.m; state.h = msg.h; state.variant = msg.variant || 'dmcfa'
      $('m').textContent = state.m; $('h').textContent = state.h; $('variant').value = state.variant
      const started = Date.now()
      const tick = () => { $('status').textContent = 'Running ' + state.variant.toUpperCase() + ' at m = ' + state.m + ', h = ' + state.h + '… ' + duration((Date.now() - started) / 1000) }
      clearInterval(timer); tick(); timer = setInterval(tick, 100)
      if (!state.report) $('main').replaceChildren()
    }
    else if (msg.type === 'report') {
      clearInterval(timer); $('status').textContent = ''
      state.report = msg.report; state.m = msg.m; state.h = msg.h; state.variant = msg.variant || 'dmcfa'; state.seconds = msg.seconds ?? 0
      if (first) { state.generated = !!msg.showGenerated; first = false }
      updateEntries(msg.report)
      render()
    }
  })
})()
</script>
</body>
</html>`
}
