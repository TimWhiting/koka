/**
 * main.ts
 *
 * Koka Playground entry point.
 *
 * Responsibilities:
 *  - Boot the Monaco editor (Koka source + read-only JS output)
 *  - Install the VFS as globalThis.kokaVFS
 *  - Register the Koka language (async — future WASM loading path)
 *  - Set up the LSP adapter scaffold (globalThis.kokaService)
 *  - Wire up "Compile & Run" (calls globalThis.kokaCompile if available)
 *  - Capture and display execution output
 */

import * as monaco from 'monaco-editor';
import { KokaVFS } from './vfs';
import { registerKokaLanguage, KOKA_LANGUAGE_ID } from './koka-lang';
import {
  registerLanguageProviders,
  type KokaLanguageService,
} from './lsp-adapter';

// ── Types ─────────────────────────────────────────────────────────────────────

/** Shape of the compiler function the WASM/JS bundle exposes. */
type KokaCompileFn = (
  moduleName: string,
  sourceText: string,
) => string | Promise<string>;

declare global {
  var kokaCompile:  KokaCompileFn       | undefined; // eslint-disable-line no-var
  var kokaService:  KokaLanguageService | undefined; // eslint-disable-line no-var
}

// ── Default sample program ────────────────────────────────────────────────────

const DEFAULT_SOURCE = `module main

fun main()
  println("Hello, Koka!")
`.trimStart();

// ── DOM references ────────────────────────────────────────────────────────────

const elSourceContainer = document.getElementById('editor-source')!;
const elJsContainer     = document.getElementById('editor-js')!;
const elConsole         = document.getElementById('console-output')!;
const elBtnRun          = document.getElementById('btn-run') as HTMLButtonElement;
const elStatusDot       = document.getElementById('status-dot')!;
const elStatusText      = document.getElementById('status-text')!;

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

// ── VFS setup ─────────────────────────────────────────────────────────────────

const vfs = new KokaVFS('/stdlib');
vfs.install();

// ── Main async initialisation ─────────────────────────────────────────────────
//
// registerKokaLanguage is async so that a future TextMate / WASM loading path
// can be added without restructuring this file.  Everything that depends on
// the editors is nested inside the IIFE.

void (async () => {
  // Register the Koka language before creating editors
  await registerKokaLanguage(monaco);

  // ── LSP adapter (scaffold — Haskell functions not yet wired up) ───────────
  //
  // The service object is mutable: the compiler bundle assigns functions to
  // its fields at runtime via globalThis.kokaService.
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

  // ── Compiler availability polling ──────────────────────────────────────────

  /**
   * Polls globalThis.kokaCompile until it becomes available, then marks the
   * playground as ready.
   */
  function watchCompilerReady(): void {
    const check = (): void => {
      if (typeof globalThis.kokaCompile === 'function') {
        setStatus('ready', 'Compiler ready');
        elBtnRun.disabled = false;
      } else {
        setTimeout(check, 500);
      }
    };
    check();
  }

  // Initially disable the button until the compiler is ready
  elBtnRun.disabled = true;
  setStatus('loading', 'Loading compiler…');
  watchCompilerReady();

  // ── Compile ────────────────────────────────────────────────────────────────

  /**
   * Populate the VFS with the editor content and invoke the compiler.
   * Returns the generated .mjs text, or null on failure.
   */
  async function compile(): Promise<string | null> {
    const sourceText = sourceEditor.getValue();

    // Derive a module name from the first "module <name>" declaration, or fall
    // back to "main".
    const moduleMatch = sourceText.match(/^\s*module\s+([a-zA-Z][a-zA-Z0-9_/-]*)/m);
    const moduleName  = moduleMatch ? moduleMatch[1] : 'main';

    // Write the source into the VFS so the compiler can read it
    const sourcePath = `/${moduleName.replace(/\//g, '/')}.kk`;
    vfs.addFile(sourcePath, sourceText);

    if (typeof globalThis.kokaCompile !== 'function') {
      appendConsole('Compiler not yet loaded. Please wait…', 'info');
      return null;
    }

    try {
      // The compiler writes its output (.mjs) into the VFS via vfs.writeFile.
      // Some implementations also return the output directly.
      const result = await Promise.resolve(
        globalThis.kokaCompile(moduleName, sourceText),
      );

      // Prefer the return value; fall back to scanning the VFS for *.mjs
      if (result && result.trim().length > 0) {
        return result;
      }

      // Scan VFS for generated .mjs files
      const written = vfs.getWrittenFiles();
      for (const [path, content] of written) {
        if (path.endsWith('.mjs') || path.endsWith('.js')) {
          return content;
        }
      }

      return null;
    } catch (err: unknown) {
      const msg = err instanceof Error ? err.message : String(err);
      appendConsole(`Compilation error: ${msg}`, 'stderr');
      return null;
    }
  }

  // ── Run ────────────────────────────────────────────────────────────────────

  /**
   * Execute generated JavaScript in an isolated context.
   * Captures console.log / console.error and redirects to the output pane.
   */
  function run(js: string): void {
    // Patch console so we can capture output
    const origLog   = console.log;
    const origError = console.error;
    const origWarn  = console.warn;

    console.log = (...args: unknown[]) => {
      origLog(...args);
      appendConsole(args.map(String).join(' '), 'stdout');
    };
    console.error = (...args: unknown[]) => {
      origError(...args);
      appendConsole(args.map(String).join(' '), 'stderr');
    };
    console.warn = (...args: unknown[]) => {
      origWarn(...args);
      appendConsole(args.map(String).join(' '), 'info');
    };

    try {
      // eslint-disable-next-line no-new-func
      const fn = new Function(js);
      fn();
    } catch (err: unknown) {
      const msg = err instanceof Error ? err.message : String(err);
      appendConsole(`Runtime error: ${msg}`, 'stderr');
    } finally {
      console.log   = origLog;
      console.error = origError;
      console.warn  = origWarn;
    }
  }

  // ── Compile & Run ──────────────────────────────────────────────────────────

  async function compileAndRun(): Promise<void> {
    if (elBtnRun.disabled) return;

    clearConsole();
    elBtnRun.disabled = true;
    setStatus('running', 'Compiling…');

    const js = await compile();

    if (js === null) {
      setStatus('error', 'Compilation failed');
      elBtnRun.disabled = false;
      return;
    }

    // Display compiled JS in the output editor
    jsEditor.setValue(js);

    setStatus('running', 'Running…');
    appendConsole('── Program output ──────────────────────────────', 'info');

    run(js);

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
      // Notify Monaco of the resize
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
