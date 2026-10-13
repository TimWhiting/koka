/*---------------------------------------------------------------------------
Interactive view of the results of the full HMCFA analysis.
See analysis/hmcfa-viewer.md in the compiler repository for the roadmap.
---------------------------------------------------------------------------*/
import * as vscode from 'vscode'

// The shape of the `koka/hmcfa` result (see Core.FlowAnalysis.Full.DMCFA.View in the compiler).
interface SourceRange { line: number, column: number, endLine: number, endColumn: number }   // 1-based, end inclusive
interface HmcfaReport { module: string, file: string, m: number, d: number, entryPoints: unknown[], error?: string }

type RunAnalysis = (filePath: string, m: number, d: number) => Promise<HmcfaReport | undefined>

export class HmcfaView implements vscode.Disposable {
  private panel?: vscode.WebviewPanel
  private file?: vscode.Uri              // the file the panel shows results for
  private statusBar: vscode.StatusBarItem
  private highlight: vscode.TextEditorDecorationType
  private subscriptions: vscode.Disposable[] = []

  constructor(private readonly runAnalysis: RunAnalysis) {
    this.statusBar = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Right, 90)
    this.statusBar.command = 'koka.setHMCFASensitivity'
    this.statusBar.tooltip = 'HMCFA timestamps keep m call sites and d handler levels. Click to change.'
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

  private get sensitivity(): { m: number, d: number } {
    const analysis = vscode.workspace.getConfiguration('koka.analysis')
    return { m: analysis.get<number>('callSensitivity') ?? 0, d: analysis.get<number>('handlerSensitivity') ?? 1 }
  }

  private updateStatusBar() {
    const { m, d } = this.sensitivity
    this.statusBar.text = `$(telescope) HMCFA m=${m} d=${d}`
    if (vscode.window.activeTextEditor?.document.languageId === 'koka' || this.panel) this.statusBar.show()
    else this.statusBar.hide()
  }

  // Change the sensitivity in the settings, and re-run the analysis if the view is open.
  async setSensitivity(m: number, d: number) {
    const analysis = vscode.workspace.getConfiguration('koka.analysis')
    const target = vscode.workspace.workspaceFolders ? vscode.ConfigurationTarget.Workspace : vscode.ConfigurationTarget.Global
    await analysis.update('callSensitivity', Math.max(0, m), target)
    await analysis.update('handlerSensitivity', Math.max(0, d), target)
    this.updateStatusBar()
    if (this.panel) await this.refresh()
  }

  // Ask for a sensitivity from the status bar.
  async pickSensitivity() {
    const { m, d } = this.sensitivity
    const presets = [[0, 0], [1, 0], [1, 1], [2, 1], [1, 2], [2, 2], [3, 3]]
    const items: (vscode.QuickPickItem & { m?: number, d?: number })[] = presets.map(([pm, pd]) => ({
      label: `m=${pm} d=${pd}`,
      description: (pm === m && pd === d ? 'current' : '') + (pm === 0 && pd === 0 ? ' context-insensitive' : ''),
      m: pm, d: pd,
    }))
    items.push({ label: 'Custom…' })
    const picked = await vscode.window.showQuickPick(items, {
      title: 'HMCFA sensitivity', placeHolder: 'm call sites and d handler levels kept in each timestamp',
    })
    if (!picked) return
    if (picked.m !== undefined && picked.d !== undefined) return this.setSensitivity(picked.m, picked.d)
    const text = await vscode.window.showInputBox({
      title: 'HMCFA sensitivity', prompt: 'm and d, separated by a space', value: `${m} ${d}`,
      validateInput: v => /^\s*\d+\s+\d+\s*$/.test(v) ? undefined : 'Enter two non-negative integers, for example: 2 1',
    })
    if (!text) return
    const [cm, cd] = text.trim().split(/\s+/).map(Number)
    return this.setSensitivity(cm, cd)
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
    const { m, d } = this.sensitivity
    this.panel.title = `HMCFA: ${this.file.path.split('/').pop()}`
    this.panel.webview.postMessage({ type: 'loading', m, d })
    let report: HmcfaReport | undefined
    try {
      report = await this.runAnalysis(this.file.fsPath, m, d)
    }
    catch (e) {
      report = { module: '', file: this.file.fsPath, m, d, entryPoints: [], error: String(e) }
    }
    if (!report) report = { module: '', file: this.file.fsPath, m, d, entryPoints: [], error: 'The Koka language server did not return a result.' }
    const showGenerated = vscode.workspace.getConfiguration('koka.analysis').get<boolean>('showGenerated') ?? false
    this.panel?.webview.postMessage({ type: 'report', report, m, d, showGenerated })
  }

  private async onMessage(msg: any) {
    switch (msg?.type) {
      case 'sensitivity': return this.setSensitivity(Number(msg.m), Number(msg.d))
      case 'refresh': return this.refresh()
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
  .performs { color: var(--vscode-descriptionForeground); }
  .arrow { color: var(--vscode-descriptionForeground); margin-right: 2px; }
  /* A timestamp: the stack from the outside in. Chips are call sites; a gate marks entering a handler or resuming. */
  .time { display: inline-flex; align-items: center; flex-wrap: wrap; gap: 3px; }
  .time > .site + .site::before, .time > .start + .site::before, .time > .more + .site::before { content: "›"; color: var(--vscode-descriptionForeground); margin-right: 3px; }
  .site { border-radius: 3px; padding: 0 4px; white-space: nowrap; border: 1px solid color-mix(in srgb, var(--vscode-charts-blue) 45%, transparent); background: color-mix(in srgb, var(--vscode-charts-blue) 9%, transparent); }
  .site.link, .gate.link { cursor: pointer; }
  .site.link:hover, .gate.link:hover { outline: 1px solid var(--vscode-focusBorder); }
  .ln { color: var(--vscode-descriptionForeground); font-size: 0.82em; margin-left: 3px; }
  .gen { color: var(--vscode-descriptionForeground); cursor: help; }
  .start, .more { color: var(--vscode-descriptionForeground); font-size: 0.9em; }
  .gate { white-space: nowrap; padding: 0 7px 0 9px; margin: 0 2px; border-radius: 0 9px 9px 0; border-left: 3px solid var(--vscode-charts-purple);
          background: color-mix(in srgb, var(--vscode-charts-purple) 16%, transparent); }
  .gate.resume { border-left-color: var(--vscode-charts-orange); background: color-mix(in srgb, var(--vscode-charts-orange) 16%, transparent); }
  .gate .what { font-size: 0.82em; color: var(--vscode-descriptionForeground); }
  .gate .eff { font-family: var(--vscode-editor-font-family); font-weight: 600; }
  .legend { display: flex; flex-wrap: wrap; gap: 4px 14px; align-items: center; color: var(--vscode-descriptionForeground); font-size: 0.9em; margin: 8px 0 2px 0; }
  .legend > span { display: inline-flex; align-items: center; gap: 5px; }
  .empty { color: var(--vscode-descriptionForeground); font-style: italic; }
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
  <label title="Number of handler levels kept in a timestamp">handler levels <b>d</b>
    <span class="stepper"><button id="d-down">−</button><span id="d">·</span><button id="d-up">+</button></span></label>
  <span class="tabs"><button id="tab-expression" class="on">Expressions</button><button id="tab-binding">Bindings</button></span>
  <input type="text" id="filter" placeholder="Filter by source text">
  <label><input type="checkbox" id="generated"> generated code</label>
  <button id="refresh">Re-run</button>
</div>
<main id="main"><p class="note">Running the analysis…</p></main>
<script nonce="${n}">
(function () {
  const vscode = acquireVsCodeApi()
  const state = { report: null, m: 0, d: 0, kind: 'expression', filter: '', generated: false }
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
      e.addEventListener('click', ev => { ev.stopPropagation(); reveal(s.range) })
    }
    return e
  }

  // The call sites of one segment of the stack, outermost first.
  // A segment that holds m sites may have lost older ones, which is shown by a leading ellipsis.
  function segment(calls, skipLast) {
    const frag = document.createDocumentFragment()
    let list = [...calls.sites].reverse()
    const cut = state.m > 0 && calls.sites.length >= state.m && !calls.sites.some(s => s.text === 'top' || s.text === 'handler')
    if (skipLast && list.length) list = list.slice(0, -1)
    if (cut || state.m === 0) {
      const more = el('span', 'more', '…')
      more.title = state.m === 0 ? 'Call sites are not tracked (m = 0)' : 'Older call sites were dropped (only the innermost ' + state.m + ' are kept)'
      frag.append(more)
    }
    for (const s of list) {
      if (s.text === 'top') { const t = el('span', 'start', 'start'); t.title = 'The start of the program'; frag.append(t) }
      else if (s.text === 'handler') continue      // the stack restarts at a delimiter: the gate before it already says so
      else frag.append(site(s))
    }
    return frag
  }

  // A delimiter: entering a handler, or resuming a continuation.
  function gate(h) {
    const g = el('span', 'gate ' + h.kind)
    g.append(el('span', 'what', (h.kind === 'resume' ? 'resume into ' : 'handle ')))
    g.append(el('span', 'eff', h.effect))
    if (h.at && h.at.range) {
      const where = el('span', 'ln', ':' + h.at.range.line + (h.others ? ' (+' + h.others + ')' : ''))
      g.append(where)
      g.classList.add('link')
      g.addEventListener('click', ev => { ev.stopPropagation(); reveal(h.at.range) })
    }
    g.title = h.kind === 'resume'
      ? 'A continuation captured by the ' + h.effect + ' handler was resumed here. To the left: the calls that led to the resume. To the right: calls made by the resumed code.'
      : 'The handler for ' + h.effect + ' was installed here' + (h.others ? ' (or at one of ' + h.others + ' other handlers for this effect)' : '') +
        '. To the left: the calls that led to installing it. To the right: calls made inside the handled code.'
    return g
  }

  // A timestamp is drawn as the stack from the outside in (left to right):
  // for each delimiter, the calls made before crossing it, then the delimiter; finally the calls made since the last one.
  function time(t) {
    const root = el('span', 'time')
    for (const h of [...t.handlers].reverse()) {
      // when resuming, the innermost call outside the delimiter is the resume call itself: the gate already shows it
      const dup = h.kind === 'resume' && h.at && h.calls.sites.length && h.calls.sites[0].text === h.at.text
      root.append(segment(h.calls, dup), gate(h))
    }
    if (!t.handlers.length && t.calls.inHandler) {
      const g = el('span', 'gate handle', 'handler'); g.title = 'Inside a handler (handler levels are not tracked: d = 0)'; root.append(g)
    }
    const inner = segment(t.calls, false)
    root.append(inner)
    if (!root.childNodes.length) root.append(el('span', 'empty', 'start'))
    return root
  }

  function values(result) {
    const box = el('div', 'values')
    box.append(el('span', 'arrow', '→'))
    for (const v of result.values) {
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
    const src = el('span', 'src'); src.append(highlight(e.text))
    head.append(el('span', 'pos', e.range.line + ':' + e.range.column), src)
    if (e.generated) { head.append(el('span', 'tag', 'generated')); if (e.kind === 'expression') head.append(el('span', 'core code', e.core)) }
    row.append(head)
    const results = el('div', 'results')
    for (const r of e.results) results.append(time(r.time), values(r))
    row.append(results)
    return row
  }

  function render() {
    $('m').textContent = state.m; $('d').textContent = state.d
    $('generated').checked = state.generated
    $('tab-expression').className = state.kind === 'expression' ? 'on' : ''
    $('tab-binding').className = state.kind === 'binding' ? 'on' : ''
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
      item(el('span', 'gate resume', 'resume into eff'), 'resumed a continuation: calls after it belong to the resumed code'))
    main.append(legend)
    const needle = state.filter.trim().toLowerCase()
    for (const ep of report.entryPoints) {
      const title = el('h2'); title.append('Entry point ', highlight(ep.name)); main.append(title)
      if (ep.timedOut) { main.append(el('p', 'note', 'The analysis did not finish within 60 seconds.')); continue }
      const all = ep.entries.filter(e => e.kind === state.kind)
      const shown = all.filter(e => (state.generated || !e.generated) && (!needle || e.text.toLowerCase().includes(needle)))
      shown.sort((a, b) => a.range.line - b.range.line || a.range.column - b.range.column || a.range.endColumn - b.range.endColumn)
      const hidden = all.filter(e => e.generated).length
      main.append(el('p', 'note', shown.length + ' ' + state.kind + 's shown' +
        (!state.generated && hidden ? ', ' + hidden + ' generated hidden' : '') + '. The analysis cache has ' + ep.cacheSize + ' entries.'))
      for (const e of shown) main.append(entry(e))
    }
  }

  const step = (dm, dd) => vscode.postMessage({ type: 'sensitivity', m: Math.max(0, state.m + dm), d: Math.max(0, state.d + dd) })
  $('m-down').addEventListener('click', () => step(-1, 0)); $('m-up').addEventListener('click', () => step(1, 0))
  $('d-down').addEventListener('click', () => step(0, -1)); $('d-up').addEventListener('click', () => step(0, 1))
  $('tab-expression').addEventListener('click', () => { state.kind = 'expression'; render() })
  $('tab-binding').addEventListener('click', () => { state.kind = 'binding'; render() })
  $('filter').addEventListener('input', ev => { state.filter = ev.target.value; render() })
  $('generated').addEventListener('change', ev => { state.generated = ev.target.checked; render() })
  $('refresh').addEventListener('click', () => vscode.postMessage({ type: 'refresh' }))

  let first = true
  window.addEventListener('message', ev => {
    const msg = ev.data
    if (msg.type === 'loading') {
      state.m = msg.m; state.d = msg.d
      $('m').textContent = state.m; $('d').textContent = state.d
      if (!state.report) $('main').replaceChildren(el('p', 'note', 'Running the analysis…'))
    }
    else if (msg.type === 'report') {
      state.report = msg.report; state.m = msg.m; state.d = msg.d
      if (first) { state.generated = !!msg.showGenerated; first = false }
      render()
    }
  })
})()
</script>
</body>
</html>`
}
