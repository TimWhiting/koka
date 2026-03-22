/**
 * main.ts
 *
 * Koka Playground entry point.
 *
 * Responsibilities:
 *  - Set up globalThis.Module (Emscripten print callbacks) BEFORE all.js runs
 *  - Boot the Monaco editor (Koka source + read-only JS output)
 *  - Install the VFS as globalThis.kokaVFS
 *  - Preload stdlib sources and precompiled .kki/.mjs files
 *  - Register the Koka language (Monaco syntax highlighting)
 *  - Set up the LSP adapter scaffold (globalThis.kokaService)
 *  - Poll for globalThis.kokaCompile and enable the run button when ready
 *  - Wire up "Compile & Run" using the actual compiler pipeline
 *  - Capture and display execution output via blob-URL ES module execution
 *  - Manage the file browser, tab bar, and resizable panels
 */

import * as monaco from 'monaco-editor';
import { KokaVFS } from './vfs';
import { registerKokaLanguage, KOKA_LANGUAGE_ID } from './koka-lang';
import {
  registerLanguageProviders,
  type KokaLanguageService,
} from './lsp-adapter';
import { runKokaModules } from './module-runner';
import { FileBrowser, buildFileTree, type FileEntry } from './file-browser';
import { loadKokaSamples, fetchGitHubDirectory } from './github-integration';

// ── Types ─────────────────────────────────────────────────────────────────────

declare global {
  // eslint-disable-next-line no-var
  var kokaCompile:         ((moduleName: string, sourceText: string) => void) | undefined;
  // eslint-disable-next-line no-var
  var kokaResult:          string | undefined;
  // eslint-disable-next-line no-var
  var kokaVerbose:         number | undefined;
  // eslint-disable-next-line no-var
  var kokaOnCompilerLog:   ((msg: string) => void) | undefined;
  // eslint-disable-next-line no-var
  var kokaService:         KokaLanguageService | undefined;
  // eslint-disable-next-line no-var
  var Module:              { print?: (t: string) => void; printErr?: (t: string) => void } | undefined;
}

// ── Emscripten Module setup ───────────────────────────────────────────────────
//
// Must be set BEFORE all.js (loaded by the hosting page) runs.
//
globalThis.Module = {
  print:    (text: string) => appendCompilerLog('[stdout] ' + text),
  printErr: (_text: string) => { /* suppress compiler stderr noise */ },
};

// ── Default sample program ────────────────────────────────────────────────────

const DEFAULT_SOURCE = `module main

fun main()
  println("Hello, Koka!")
`.trimStart();

// ── DOM references ────────────────────────────────────────────────────────────

const elSourceContainer    = document.getElementById('editor-source')!;
const elJsContainer        = document.getElementById('editor-js')!;
const elConsole            = document.getElementById('console-output')!;
const elCompilerLog        = document.getElementById('compiler-log-output')!;
const elBtnRun             = document.getElementById('btn-run') as HTMLButtonElement;
const elStatusDot          = document.getElementById('status-dot')!;
const elStatusText         = document.getElementById('status-text')!;
const elVerboseSelect      = document.getElementById('verbose-level') as HTMLSelectElement;
const elLogVfsCheckbox     = document.getElementById('log-vfs') as HTMLInputElement;
const elTabBar             = document.getElementById('tab-bar')!;
const elBtnFileBrowser     = document.getElementById('btn-filebrowser') as HTMLButtonElement;
const elFileBrowserPanel   = document.getElementById('file-browser-panel')!;
const elFileBrowserTree    = document.getElementById('file-browser-tree')!;
const elCompilerLogArea    = document.getElementById('compiler-log-area')!;
const elCompilerLogToggle  = document.getElementById('compiler-log-toggle')!;
const elCompilerLogBody    = document.getElementById('compiler-log-body')!;
const elCompilerLogArrow   = document.getElementById('compiler-log-toggle-arrow')!;
const elResizeHandleLog    = document.getElementById('resize-handle-log')!;

// ── Status helper ─────────────────────────────────────────────────────────────

type StatusKind = 'loading' | 'ready' | 'error' | 'running';

function setStatus(kind: StatusKind, text: string): void {
  elStatusDot.className = kind;
  elStatusText.textContent = text;
}

// ── Console output helper ─────────────────────────────────────────────────────

function clearConsole(): void {
  elConsole.innerHTML = '';
}

function appendConsole(
  text: string,
  cls: 'stdout' | 'stderr' | 'info' | 'separator' = 'stdout',
): void {
  const line = document.createElement('span');
  line.className = `console-line ${cls}`;
  line.textContent = text;
  elConsole.appendChild(line);
  elConsole.scrollTop = elConsole.scrollHeight;
}

// ── Compiler log helper ───────────────────────────────────────────────────────

function clearCompilerLog(): void {
  elCompilerLog.textContent = '';
}

function appendCompilerLog(msg: string): void {
  elCompilerLog.textContent += msg + '\n';
  elCompilerLog.scrollTop = elCompilerLog.scrollHeight;
  // Auto-expand the log when there's output
  if (elCompilerLogArea.classList.contains('collapsed')) {
    elCompilerLogArea.classList.remove('collapsed');
    elCompilerLogArrow.textContent = '▾';
  }
}

// Register the compiler log callback so the compiler can stream messages
globalThis.kokaOnCompilerLog = (msg: string) => {
  appendCompilerLog(msg);
};

// ── VFS setup ─────────────────────────────────────────────────────────────────

const vfs = new KokaVFS();
vfs.install();

if (elLogVfsCheckbox) {
  elLogVfsCheckbox.addEventListener('change', () => {
    vfs.logVfs = elLogVfsCheckbox.checked;
  });
}

// ── Tab management ────────────────────────────────────────────────────────────

interface TabEntry {
  id: string;
  name: string;
  path: string;
  model: monaco.editor.ITextModel;
}

const openTabs = new Map<string, TabEntry>();
let activeTabId: string | null = null;

/** Generate a unique tab ID */
function makeTabId(): string {
  return 'tab-' + Math.random().toString(36).slice(2, 9);
}

/** Create a new tab (or switch to existing one with same path) */
function openFile(path: string, content: string, name: string): void {
  // Check if already open by path
  for (const tab of openTabs.values()) {
    if (tab.path === path) {
      switchTab(tab.id);
      return;
    }
  }

  const id = makeTabId();
  const uri = monaco.Uri.parse(`koka://playground/${path}`);
  let model = monaco.editor.getModel(uri);
  if (!model) {
    const language = path.endsWith('.kk') || path.endsWith('.kki')
      ? KOKA_LANGUAGE_ID
      : 'plaintext';
    model = monaco.editor.createModel(content, language, uri);
  } else {
    model.setValue(content);
  }

  openTabs.set(id, { id, name, path, model });
  renderTabs();
  switchTab(id);
}

/** Close a tab by ID */
function closeTab(id: string): void {
  const tab = openTabs.get(id);
  if (!tab) return;

  // Don't destroy the model if it's the default tab — just reset content
  openTabs.delete(id);

  if (activeTabId === id) {
    // Switch to another tab, or create a fallback
    const remaining = [...openTabs.keys()];
    if (remaining.length > 0) {
      switchTab(remaining[remaining.length - 1]);
    } else {
      // Reopen default
      openFile('main.kk', DEFAULT_SOURCE, 'main.kk');
      return; // openFile calls renderTabs + switchTab
    }
  }

  renderTabs();
}

/** Switch editor to the given tab */
function switchTab(id: string): void {
  const tab = openTabs.get(id);
  if (!tab) return;
  activeTabId = id;

  if (sourceEditor) {
    sourceEditor.setModel(tab.model);
  }

  renderTabs();
}

/** Re-render the tab bar DOM */
function renderTabs(): void {
  elTabBar.innerHTML = '';
  for (const tab of openTabs.values()) {
    const tabEl = document.createElement('div');
    tabEl.className = 'tab' + (tab.id === activeTabId ? ' active' : '');
    tabEl.setAttribute('data-tab-id', tab.id);
    tabEl.setAttribute('title', tab.path);

    const nameEl = document.createElement('span');
    nameEl.className = 'tab-name';
    nameEl.textContent = tab.name;

    const closeEl = document.createElement('span');
    closeEl.className = 'tab-close';
    closeEl.textContent = '×';
    closeEl.setAttribute('title', 'Close tab');

    closeEl.addEventListener('click', (e: MouseEvent) => {
      e.stopPropagation();
      closeTab(tab.id);
    });

    tabEl.appendChild(nameEl);
    tabEl.appendChild(closeEl);

    tabEl.addEventListener('click', () => { switchTab(tab.id); });

    elTabBar.appendChild(tabEl);
  }
}

// ── File browser setup ────────────────────────────────────────────────────────

const fileBrowser = new FileBrowser(elFileBrowserTree, {
  onFileSelect: (path, content, name) => {
    openFile(path, content, name);
  },
  onJsFileSelect: (_path, content, name) => {
    jsEditor.setValue(content);
    appendConsole(`Viewing ${name}`, 'info');
  },
  onDirectoryExpand: async (entry) => {
    // Lazy-load directory contents from GitHub
    return fetchGitHubDirectory('koka-lang', 'koka', entry.path);
  },
});

// Placeholder samples section
fileBrowser.addSection('Samples', []);
fileBrowser.addSection('Open Files', []);
fileBrowser.addSection('VFS', []);

// Load samples from GitHub asynchronously
void loadKokaSamples()
  .then((entries) => {
    fileBrowser.updateSection('Samples', entries);
  })
  .catch(() => {
    fileBrowser.updateSection('Samples', [
      { name: 'hello.kk', path: 'samples/hello.kk', type: 'file' },
      { name: 'fibonacci.kk', path: 'samples/fibonacci.kk', type: 'file' },
    ]);
  });

/** Refresh the Open Files section in the file browser */
function refreshOpenFilesSection(): void {
  const entries: FileEntry[] = [];
  for (const tab of openTabs.values()) {
    entries.push({ name: tab.name, path: tab.path, type: 'file' });
  }
  fileBrowser.updateSection('Open Files', entries);
}

/** Refresh the VFS section in the file browser (debug listing) */
function refreshVfsSection(): void {
  const written = vfs.getWrittenFiles();
  // Build a proper tree, only showing compiler output (not preloaded stdlib)
  const tree = buildFileTree(written, (path) =>
    path.includes('.koka/') && (path.endsWith('.mjs') || path.endsWith('.kki'))
  );
  fileBrowser.updateSection('VFS Output', tree);
}

// ── File browser toggle ───────────────────────────────────────────────────────

function setFileBrowserVisible(visible: boolean): void {
  if (visible) {
    elFileBrowserPanel.classList.remove('collapsed');
    elBtnFileBrowser.classList.add('active');
  } else {
    elFileBrowserPanel.classList.add('collapsed');
    elBtnFileBrowser.classList.remove('active');
  }
  // Trigger Monaco layout update after transition
  setTimeout(() => {
    sourceEditor?.layout();
    jsEditor?.layout();
  }, 220);
}

elBtnFileBrowser.addEventListener('click', () => {
  const isVisible = !elFileBrowserPanel.classList.contains('collapsed');
  setFileBrowserVisible(!isVisible);
});

// ── Compiler log collapse/expand ──────────────────────────────────────────────

elCompilerLogToggle.addEventListener('click', () => {
  const collapsed = elCompilerLogArea.classList.toggle('collapsed');
  elCompilerLogArrow.textContent = collapsed ? '▸' : '▾';
  // Give Monaco a moment to adapt
  setTimeout(() => {
    sourceEditor?.layout();
    jsEditor?.layout();
  }, 50);
});

// ── Main async initialisation ─────────────────────────────────────────────────

// These are used before the async block below, so we declare them here.
// eslint-disable-next-line prefer-const
let sourceEditor: monaco.editor.IStandaloneCodeEditor = null!;
// eslint-disable-next-line prefer-const
let jsEditor: monaco.editor.IStandaloneCodeEditor = null!;

void (async () => {
  // Register the Koka language before creating editors
  await registerKokaLanguage(monaco);

  // ── LSP adapter (scaffold) ─────────────────────────────────────────────
  const kokaService: KokaLanguageService = {};
  registerLanguageProviders(monaco, KOKA_LANGUAGE_ID, kokaService);
  globalThis.kokaService = kokaService;

  // ── Editor options ─────────────────────────────────────────────────────

  const EDITOR_COMMON_OPTIONS: monaco.editor.IEditorConstructionOptions = {
    theme: 'vs-dark',
    fontSize: 14,
    fontFamily: "'Cascadia Code', 'Fira Code', 'Consolas', 'Courier New', monospace",
    fontLigatures: true,
    minimap: { enabled: false },
    scrollBeyondLastLine: false,
    renderLineHighlight: 'all',
    lineNumbers: 'on',
    glyphMargin: false,
    folding: true,
    automaticLayout: true,
  };

  sourceEditor = monaco.editor.create(elSourceContainer, {
    ...EDITOR_COMMON_OPTIONS,
    value: DEFAULT_SOURCE,
    language: KOKA_LANGUAGE_ID,
    tabSize: 2,
    insertSpaces: true,
    wordWrap: 'off',
  });

  jsEditor = monaco.editor.create(elJsContainer, {
    ...EDITOR_COMMON_OPTIONS,
    value: '',
    language: 'javascript',
    readOnly: true,
    lineNumbers: 'on',
    wordWrap: 'off',
    scrollBeyondLastLine: false,
  });

  // ── Open default tab ───────────────────────────────────────────────────
  //
  // We must create the tab after sourceEditor exists so switchTab can call
  // sourceEditor.setModel().
  openFile('main.kk', DEFAULT_SOURCE, 'main.kk');

  // ── Keyboard shortcut: Ctrl+Enter / Cmd+Enter to compile & run ─────────

  sourceEditor.addCommand(
    monaco.KeyMod.CtrlCmd | monaco.KeyCode.Enter,
    () => { void compileAndRun(); },
  );

  // ── Ctrl+B to toggle file browser ──────────────────────────────────────

  sourceEditor.addCommand(
    monaco.KeyMod.CtrlCmd | monaco.KeyCode.KeyB,
    () => {
      const isVisible = !elFileBrowserPanel.classList.contains('collapsed');
      setFileBrowserVisible(!isVisible);
    },
  );

  // ── Preloading ─────────────────────────────────────────────────────────

  elBtnRun.disabled = true;
  setStatus('loading', 'Loading stdlib…');

  try {
    const [srcCount, preCount] = await Promise.all([
      vfs.preloadSources('', 'stdlib-manifest.json')
        .catch((e: unknown) => { appendCompilerLog('[warn] stdlib preload: ' + String(e)); return 0; }),
      vfs.preloadPrecompiled('', 'precompiled-manifest.json')
        .catch((e: unknown) => { appendCompilerLog('[warn] precompiled preload: ' + String(e)); return 0; }),
    ]);

    appendConsole(
      `Loaded ${srcCount} stdlib source files + ${preCount} precompiled files.`,
      'info',
    );
  } catch (e: unknown) {
    appendConsole('Warning: could not preload stdlib: ' + String(e), 'info');
  }

  setStatus('loading', 'Waiting for compiler…');

  // ── Compiler availability polling ──────────────────────────────────────

  function watchCompilerReady(): void {
    const check = (): void => {
      if (typeof globalThis.kokaCompile === 'function') {
        setStatus('ready', 'Compiler ready');
        elBtnRun.disabled = false;
        appendConsole('Compiler ready!', 'info');
      } else {
        setTimeout(check, 500);
      }
    };
    check();
  }

  watchCompilerReady();

  // ── Compile ────────────────────────────────────────────────────────────

  /**
   * Invoke the Koka compiler on the current editor source.
   * Returns the generated main module name on success, or null on failure.
   */
  async function compile(sourceText: string): Promise<string | null> {
    if (typeof globalThis.kokaCompile !== 'function') {
      appendConsole('Compiler not yet loaded. Please wait…', 'info');
      return null;
    }

    globalThis.kokaVerbose = parseInt(elVerboseSelect?.value ?? '1', 10) || 0;

    vfs.clearGenerated();
    globalThis.kokaResult = undefined;

    const moduleMatch = sourceText.match(/^\s*module\s+([a-zA-Z][a-zA-Z0-9_/-]*)/m);
    const moduleName  = moduleMatch ? moduleMatch[1] : 'main';

    globalThis.kokaCompile(moduleName, sourceText);

    const resultJson = await new Promise<string>((resolve, reject) => {
      let elapsed = 0;
      const poll = setInterval(() => {
        elapsed += 50;
        if (globalThis.kokaResult !== undefined) {
          clearInterval(poll);
          resolve(globalThis.kokaResult as string);
        } else if (elapsed > 30_000) {
          clearInterval(poll);
          reject(new Error('Compilation timed out after 30 s'));
        }
      }, 50);
    });

    let parsed: { success: boolean; errors?: string[] };
    try {
      parsed = JSON.parse(resultJson) as typeof parsed;
    } catch {
      appendConsole('Error: could not parse compiler result: ' + resultJson, 'stderr');
      return null;
    }

    if (!parsed.success) {
      appendConsole('=== Compilation Errors ===', 'stderr');
      for (const err of parsed.errors ?? []) {
        appendConsole(err, 'stderr');
      }
      return null;
    }

    return moduleName;
  }

  // ── Run ────────────────────────────────────────────────────────────────

  async function run(moduleName: string): Promise<void> {
    const generatedMjs = vfs.getGeneratedMjs();

    if (generatedMjs.size === 0) {
      appendConsole('No .mjs output found after compilation.', 'stderr');
      return;
    }

    for (const [path, code] of generatedMjs) {
      const filename = path.split('/').pop() ?? path;
      if (filename === moduleName + '.mjs' || filename === 'main.mjs') {
        jsEditor.setValue(code);
        appendConsole(
          `Generated ${filename}: ${code.length} chars`,
          'info',
        );
        break;
      }
    }

    await runKokaModules(
      vfs.getPrecompiledMjs(),
      generatedMjs,
      moduleName,
      (text) => appendConsole(text, 'stdout'),
      (text) => appendConsole(text, 'stderr'),
    );

    // Refresh VFS section after compilation
    refreshVfsSection();
  }

  // ── Compile & Run ──────────────────────────────────────────────────────

  async function compileAndRun(): Promise<void> {
    if (elBtnRun.disabled) return;

    clearConsole();
    clearCompilerLog();
    elBtnRun.disabled = true;
    setStatus('running', 'Compiling…');

    // Always compile from the active tab's content
    const sourceText = sourceEditor.getValue();

    try {
      const moduleName = await compile(sourceText);

      if (moduleName === null) {
        setStatus('error', 'Compilation failed');
        elBtnRun.disabled = false;
        return;
      }

      appendConsole('Compilation successful!', 'info');
      setStatus('running', 'Running…');

      await run(moduleName);
    } catch (err: unknown) {
      const msg = err instanceof Error ? err.message : String(err);
      appendConsole('ERROR: ' + msg, 'stderr');
      setStatus('error', 'Error');
    }

    setStatus('ready', 'Compiler ready');
    elBtnRun.disabled = false;
  }

  // ── Button handler ─────────────────────────────────────────────────────

  elBtnRun.addEventListener('click', () => { void compileAndRun(); });

  // ── Drag-to-resize: horizontal (source | output) ───────────────────────

  (function setupHorizontalResize(): void {
    const handle     = document.getElementById('resize-handle-h')!;
    const paneSource = document.getElementById('pane-source')!;
    const panels     = document.getElementById('editor-panels')!;

    let dragging   = false;
    let startX     = 0;
    let startWidth = 0;

    handle.addEventListener('mousedown', (e: MouseEvent) => {
      dragging   = true;
      startX     = e.clientX;
      startWidth = paneSource.getBoundingClientRect().width;
      handle.classList.add('dragging');
      document.body.style.cursor = 'col-resize';
      document.body.style.userSelect = 'none';
      e.preventDefault();
    });

    document.addEventListener('mousemove', (e: MouseEvent) => {
      if (!dragging) return;
      const totalWidth = panels.getBoundingClientRect().width;
      const delta      = e.clientX - startX;
      const newWidth   = Math.min(
        Math.max(startWidth + delta, 200),
        totalWidth - 200,
      );
      paneSource.style.width = `${newWidth}px`;
      sourceEditor.layout();
      jsEditor.layout();
    });

    document.addEventListener('mouseup', () => {
      if (!dragging) return;
      dragging = false;
      handle.classList.remove('dragging');
      document.body.style.cursor = '';
      document.body.style.userSelect = '';
    });
  })();

  // ── Drag-to-resize: vertical (JS output | console) ────────────────────

  (function setupVerticalResize(): void {
    const handle     = document.getElementById('resize-handle-v')!;
    const paneConsole = document.getElementById('pane-console')!;
    const paneOutput  = document.getElementById('pane-output')!;

    let dragging    = false;
    let startY      = 0;
    let startHeight = 0;

    handle.addEventListener('mousedown', (e: MouseEvent) => {
      dragging    = true;
      startY      = e.clientY;
      startHeight = paneConsole.getBoundingClientRect().height;
      handle.classList.add('dragging');
      document.body.style.cursor = 'row-resize';
      document.body.style.userSelect = 'none';
      e.preventDefault();
    });

    document.addEventListener('mousemove', (e: MouseEvent) => {
      if (!dragging) return;
      const totalHeight = paneOutput.getBoundingClientRect().height;
      const delta       = startY - e.clientY;
      const newHeight   = Math.min(
        Math.max(startHeight + delta, 60),
        totalHeight - 80,
      );
      paneConsole.style.height = `${newHeight}px`;
      jsEditor.layout();
    });

    document.addEventListener('mouseup', () => {
      if (!dragging) return;
      dragging = false;
      handle.classList.remove('dragging');
      document.body.style.cursor = '';
      document.body.style.userSelect = '';
    });
  })();

  // ── Drag-to-resize: file browser width ────────────────────────────────

  (function setupFileBrowserResize(): void {
    const handle = document.getElementById('resize-handle-fb')!;
    const panel  = document.getElementById('file-browser-panel')!;

    let dragging   = false;
    let startX     = 0;
    let startWidth = 0;

    handle.addEventListener('mousedown', (e: MouseEvent) => {
      if (panel.classList.contains('collapsed')) return;
      dragging   = true;
      startX     = e.clientX;
      startWidth = panel.getBoundingClientRect().width;
      handle.classList.add('dragging');
      document.body.style.cursor = 'col-resize';
      document.body.style.userSelect = 'none';
      e.preventDefault();
    });

    document.addEventListener('mousemove', (e: MouseEvent) => {
      if (!dragging) return;
      const delta    = e.clientX - startX;
      const newWidth = Math.min(Math.max(startWidth + delta, 140), 500);
      panel.style.width = `${newWidth}px`;
      sourceEditor.layout();
      jsEditor.layout();
    });

    document.addEventListener('mouseup', () => {
      if (!dragging) return;
      dragging = false;
      handle.classList.remove('dragging');
      document.body.style.cursor = '';
      document.body.style.userSelect = '';
    });
  })();

  // ── Drag-to-resize: compiler log height ───────────────────────────────

  (function setupCompilerLogResize(): void {
    const handle  = elResizeHandleLog;
    const logBody = elCompilerLogBody;

    let dragging    = false;
    let startY      = 0;
    let startHeight = 0;

    handle.addEventListener('mousedown', (e: MouseEvent) => {
      if (elCompilerLogArea.classList.contains('collapsed')) return;
      dragging    = true;
      startY      = e.clientY;
      startHeight = logBody.getBoundingClientRect().height;
      handle.classList.add('dragging');
      document.body.style.cursor = 'row-resize';
      document.body.style.userSelect = 'none';
      e.preventDefault();
    });

    document.addEventListener('mousemove', (e: MouseEvent) => {
      if (!dragging) return;
      const delta     = startY - e.clientY;
      const newHeight = Math.min(Math.max(startHeight + delta, 40), 500);
      logBody.style.height = `${newHeight}px`;
      sourceEditor.layout();
      jsEditor.layout();
    });

    document.addEventListener('mouseup', () => {
      if (!dragging) return;
      dragging = false;
      handle.classList.remove('dragging');
      document.body.style.cursor = '';
      document.body.style.userSelect = '';
    });
  })();

  // ── Keep "Open Files" section in sync with tabs ────────────────────────

  // Use a MutationObserver on the tab bar to keep the file browser in sync
  new MutationObserver(() => { refreshOpenFilesSection(); })
    .observe(elTabBar, { childList: true });

})();
