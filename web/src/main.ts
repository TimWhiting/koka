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
 */

import * as monaco from 'monaco-editor';
import { KokaVFS } from './vfs';
import { registerKokaLanguage, KOKA_LANGUAGE_ID } from './koka-lang';
import {
  registerLanguageProviders,
  type KokaLanguageService,
} from './lsp-adapter';
import { runKokaModules } from './module-runner';

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
// We create it here so that when the hosting page's <script src="all.js"> fires
// it already finds globalThis.Module with the right callbacks.
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

const elSourceContainer = document.getElementById('editor-source')!;
const elJsContainer     = document.getElementById('editor-js')!;
const elConsole         = document.getElementById('console-output')!;
const elCompilerLog     = document.getElementById('compiler-log-output')!;
const elBtnRun          = document.getElementById('btn-run') as HTMLButtonElement;
const elStatusDot       = document.getElementById('status-dot')!;
const elStatusText      = document.getElementById('status-text')!;
const elVerboseSelect   = document.getElementById('verbose-level') as HTMLSelectElement;
const elLogVfsCheckbox  = document.getElementById('log-vfs') as HTMLInputElement;

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
}

// Register the compiler log callback so the compiler can stream messages
globalThis.kokaOnCompilerLog = (msg: string) => {
  appendCompilerLog(msg);
};

// ── VFS setup ─────────────────────────────────────────────────────────────────

const vfs = new KokaVFS();
vfs.install();

// Keep VFS logVfs in sync with the checkbox
if (elLogVfsCheckbox) {
  elLogVfsCheckbox.addEventListener('change', () => {
    vfs.logVfs = elLogVfsCheckbox.checked;
  });
}

// ── Main async initialisation ─────────────────────────────────────────────────

void (async () => {
  // Register the Koka language before creating editors
  await registerKokaLanguage(monaco);

  // ── LSP adapter (scaffold — Haskell functions not yet wired up) ───────────
  const kokaService: KokaLanguageService = {};
  registerLanguageProviders(monaco, KOKA_LANGUAGE_ID, kokaService);
  globalThis.kokaService = kokaService;

  // ── Editor options ─────────────────────────────────────────────────────────

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

  const sourceEditor = monaco.editor.create(elSourceContainer, {
    ...EDITOR_COMMON_OPTIONS,
    value: DEFAULT_SOURCE,
    language: KOKA_LANGUAGE_ID,
    tabSize: 2,
    insertSpaces: true,
    wordWrap: 'off',
  });

  const jsEditor = monaco.editor.create(elJsContainer, {
    ...EDITOR_COMMON_OPTIONS,
    value: '',
    language: 'javascript',
    readOnly: true,
    lineNumbers: 'on',
    wordWrap: 'off',
    scrollBeyondLastLine: false,
  });

  // ── Keyboard shortcut: Ctrl+Enter / Cmd+Enter to compile & run ─────────────

  sourceEditor.addCommand(
    monaco.KeyMod.CtrlCmd | monaco.KeyCode.Enter,
    () => { void compileAndRun(); },
  );

  // ── Preloading ─────────────────────────────────────────────────────────────
  //
  // We detect the base URL from the current page location.  When the hosting
  // page is the koka-playground.jsexe/index.html the manifests live alongside
  // it; when using the Vite dev server the manifests are served from public/.

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

  // ── Compiler availability polling ──────────────────────────────────────────
  //
  // all.js is loaded by the hosting page via a <script> tag.  We poll until
  // globalThis.kokaCompile becomes available.

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

  // ── Compile ────────────────────────────────────────────────────────────────

  /**
   * Invoke the Koka compiler on the current editor source.
   * Returns the generated main module name on success, or null on failure.
   */
  async function compile(sourceText: string): Promise<string | null> {
    if (typeof globalThis.kokaCompile !== 'function') {
      appendConsole('Compiler not yet loaded. Please wait…', 'info');
      return null;
    }

    // Apply verbose level from toolbar
    globalThis.kokaVerbose = parseInt(elVerboseSelect?.value ?? '1', 10) || 0;

    // Clear previous compilation artifacts from VFS
    vfs.clearGenerated();

    // Reset the result slot
    globalThis.kokaResult = undefined;

    // Derive module name from "module <name>" declaration or fall back to "main"
    const moduleMatch = sourceText.match(/^\s*module\s+([a-zA-Z][a-zA-Z0-9_/-]*)/m);
    const moduleName  = moduleMatch ? moduleMatch[1] : 'main';

    // Kick off compilation (async — spawns Haskell thread internally)
    globalThis.kokaCompile(moduleName, sourceText);

    // Poll for result (set by the compiler on globalThis.kokaResult)
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

  // ── Run ────────────────────────────────────────────────────────────────────

  /**
   * Execute the compiled ES modules.
   * Collects generated .mjs from VFS plus precompiled stdlib .mjs, then
   * runs them via blob-URL dynamic imports.
   */
  async function run(moduleName: string): Promise<void> {
    const generatedMjs = vfs.getGeneratedMjs();

    if (generatedMjs.size === 0) {
      appendConsole('No .mjs output found after compilation.', 'stderr');
      return;
    }

    // Show the main generated module in the JS editor
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
  }

  // ── Compile & Run ──────────────────────────────────────────────────────────

  async function compileAndRun(): Promise<void> {
    if (elBtnRun.disabled) return;

    clearConsole();
    clearCompilerLog();
    elBtnRun.disabled = true;
    setStatus('running', 'Compiling…');

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

  // ── Button handler ─────────────────────────────────────────────────────────

  elBtnRun.addEventListener('click', () => { void compileAndRun(); });

  // ── Drag-to-resize panes ───────────────────────────────────────────────────

  (function setupResizeHandle(): void {
    const handle     = document.getElementById('resize-handle')!;
    const paneSource = document.getElementById('pane-source')!;
    const main       = document.getElementById('main')!;

    let dragging = false;
    let startX = 0;
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
      const totalWidth = main.getBoundingClientRect().width;
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
})();
