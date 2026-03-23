/**
 * shared-compiler.ts
 *
 * Manages a single WASM compiler instance shared by all <koka-editor> elements
 * on the page. Lazily loaded on first compile request.
 */

import {
  WASI,
  File,
  Directory,
  PreopenDirectory,
  ConsoleStdout,
  OpenFile,
} from '@bjorn3/browser_wasi_shim';

export interface SharedCompiler {
  compile: (moduleName: string, sourceText: string) => Promise<CompileResult>;
  run: (moduleName: string, generatedFiles: Map<string, string>) => Promise<string>;
}

export interface CompileResult {
  success: boolean;
  stdout: string;
  stderr: string;
  generatedFiles: Map<string, string>;
}

let sharedInstance: SharedCompiler | null = null;
let loading: Promise<SharedCompiler | null> | null = null;

/**
 * Get or create the shared WASM compiler.
 * All <koka-editor> elements on the page share this instance.
 */
export async function getSharedCompiler(): Promise<SharedCompiler | null> {
  if (sharedInstance) return sharedInstance;
  if (loading) return loading;

  loading = initCompiler();
  sharedInstance = await loading;
  return sharedInstance;
}

async function initCompiler(): Promise<SharedCompiler | null> {
  try {
    // Find the WASM URL — look for a script tag or use default
    const wasmUrl = findWasmUrl();
    const stdlibUrl = findStdlibUrl();

    // Load stdlib sources and precompiled files
    const { sources, precompiled } = await loadStdlib(stdlibUrl);

    // Load and compile the WASM module
    const response = await fetch(wasmUrl);
    if (!response.ok) throw new Error(`Failed to fetch ${wasmUrl}: ${response.status}`);
    const bytes = await response.arrayBuffer();
    const wasmModule = await WebAssembly.compile(bytes);

    return {
      compile: (moduleName, sourceText) =>
        compileWithWasm(wasmModule, moduleName, sourceText, sources, precompiled),
      run: (moduleName, generatedFiles) =>
        runModules(moduleName, generatedFiles, precompiled),
    };
  } catch (err) {
    console.error('[koka-editor] Failed to initialize compiler:', err);
    return null;
  }
}

// ── URL discovery ───────────────────────────────────────────────────────────

function findWasmUrl(): string {
  // Check for data attribute on the script tag or a meta tag
  const meta = document.querySelector('meta[name="koka-wasm-url"]');
  if (meta) return meta.getAttribute('content') || '';

  // Check for a global config
  const cfg = (globalThis as Record<string, unknown>).kokaConfig as Record<string, string> | undefined;
  if (cfg?.wasmUrl) return cfg.wasmUrl;

  // Default: same directory as the page
  return 'koka-playground.wasm';
}

function findStdlibUrl(): string {
  const meta = document.querySelector('meta[name="koka-stdlib-url"]');
  if (meta) return meta.getAttribute('content') || '';

  const cfg = (globalThis as Record<string, unknown>).kokaConfig as Record<string, string> | undefined;
  if (cfg?.stdlibUrl) return cfg.stdlibUrl;

  return '';  // same origin
}

// ── Stdlib loading ──────────────────────────────────────────────────────────

async function loadStdlib(baseUrl: string): Promise<{
  sources: Map<string, string>;
  precompiled: Map<string, string>;
}> {
  const sources = new Map<string, string>();
  const precompiled = new Map<string, string>();
  const prefix = baseUrl ? baseUrl.replace(/\/$/, '') + '/' : '';

  // Load stdlib manifest
  try {
    const resp = await fetch(prefix + 'stdlib-manifest.json');
    if (resp.ok) {
      const files: string[] = await resp.json();
      await Promise.all(files.map(async (f) => {
        try {
          const r = await fetch(prefix + 'lib/' + f);
          if (r.ok) sources.set(f, await r.text());
        } catch { /* skip */ }
      }));
    }
  } catch { /* no manifest */ }

  // Load precompiled manifest
  try {
    const resp = await fetch(prefix + 'precompiled-manifest.json');
    if (resp.ok) {
      const files: string[] = await resp.json();
      await Promise.all(files.map(async (f) => {
        try {
          const r = await fetch(prefix + 'precompiled/' + f);
          if (r.ok) precompiled.set(f, await r.text());
        } catch { /* skip */ }
      }));
    }
  } catch { /* no manifest */ }

  return { sources, precompiled };
}

// ── WASM compilation ────────────────────────────────────────────────────────

function buildDirectoryTree(files: Map<string, string>): Directory {
  const root = new Map<string, File | Directory>();
  for (const [path, content] of files) {
    const parts = path.split('/').filter(Boolean);
    let current = root;
    for (let i = 0; i < parts.length - 1; i++) {
      if (!current.has(parts[i])) {
        current.set(parts[i], new Directory(new Map()));
      }
      const dir = current.get(parts[i]);
      if (dir instanceof Directory) current = dir.contents as Map<string, File | Directory>;
    }
    const filename = parts[parts.length - 1];
    if (filename) current.set(filename, new File(new TextEncoder().encode(content)));
  }
  return new Directory(root);
}

function collectFiles(dir: Directory, prefix: string, out: Map<string, string>, dec: TextDecoder): void {
  for (const [name, entry] of dir.contents) {
    const path = prefix ? prefix + '/' + name : name;
    if (entry instanceof File) out.set(path, dec.decode(entry.data));
    else if (entry instanceof Directory) collectFiles(entry, path, out, dec);
  }
}

async function compileWithWasm(
  wasmModule: WebAssembly.Module,
  moduleName: string,
  sourceText: string,
  sources: Map<string, string>,
  precompiled: Map<string, string>,
): Promise<CompileResult> {
  // Build WASI filesystem
  const shareLibFiles = new Map<string, string>();
  for (const [path, content] of sources) {
    shareLibFiles.set(path, content);
  }

  const libFiles = new Map<string, string>();
  for (const [f, content] of precompiled) {
    libFiles.set('js-debug/' + f, content);
  }

  // Add user source
  const rootFiles = new Map<string, string>();
  rootFiles.set(moduleName.replace(/\//g, '/') + '.kk', sourceText);

  const shareLibDir = buildDirectoryTree(shareLibFiles);
  const libDir = buildDirectoryTree(libFiles);
  const rootDir = buildDirectoryTree(rootFiles);
  const outputContents = new Map<string, File | Directory>();

  const stdinFile = new File(new TextEncoder().encode(''));
  const stdoutLines: string[] = [];
  const stderrLines: string[] = [];

  const wasi = new WASI(
    ['koka-playground', moduleName],
    [],
    [
      new OpenFile(stdinFile),
      ConsoleStdout.lineBuffered((line) => stdoutLines.push(line)),
      ConsoleStdout.lineBuffered((line) => stderrLines.push(line)),
      new PreopenDirectory('/', rootDir.contents as Map<string, File | Directory>),
      new PreopenDirectory('/share/lib', shareLibDir.contents as Map<string, File | Directory>),
      new PreopenDirectory('/lib', libDir.contents as Map<string, File | Directory>),
      new PreopenDirectory('/.koka', outputContents),
    ],
    { debug: false },
  );

  const instance = new WebAssembly.Instance(wasmModule, {
    wasi_snapshot_preview1: wasi.wasiImport,
  });

  try {
    wasi.start(instance as unknown as { exports: { memory: WebAssembly.Memory; _start: () => void } });
  } catch (e) {
    if (!(e instanceof Error && e.message?.includes('exit'))) {
      stderrLines.push(String(e));
    }
  }

  const generatedFiles = new Map<string, string>();
  const decoder = new TextDecoder();
  collectFiles(new Directory(outputContents), '', generatedFiles, decoder);

  const stdout = stdoutLines.join('\n');
  const stderr = stderrLines.join('\n');
  let success = false;
  try {
    success = JSON.parse(stdout).success === true;
  } catch { /* */ }

  return { success, stdout, stderr, generatedFiles };
}

// ── Module execution ────────────────────────────────────────────────────────

function kokaModuleToFilename(moduleName: string): string {
  let result = '';
  for (const c of moduleName) {
    if (/[a-zA-Z0-9]/.test(c)) result += c;
    else if (c === '/') result += '_';
    else if (c === '-') result += '_dash_';
    else if (c === '_') result += '__';
    else if (c === '.') result += '_dot_';
    else result += c;
  }
  return result;
}

async function runModules(
  moduleName: string,
  generatedFiles: Map<string, string>,
  precompiled: Map<string, string>,
): Promise<string> {
  // Build a map of module URLs (blob URLs)
  const moduleUrls = new Map<string, string>();

  // Add precompiled .mjs
  for (const [name, content] of precompiled) {
    if (name.endsWith('.mjs')) {
      const blob = new Blob([content], { type: 'application/javascript' });
      moduleUrls.set(name, URL.createObjectURL(blob));
    }
  }

  // Add generated .mjs (override precompiled if same name)
  for (const [path, content] of generatedFiles) {
    if (path.endsWith('.mjs')) {
      const name = path.split('/').pop()!;
      const blob = new Blob([content], { type: 'application/javascript' });
      moduleUrls.set(name, URL.createObjectURL(blob));
    }
  }

  // Find the main module
  const mainFilename = kokaModuleToFilename(moduleName) + '.mjs';
  // Also check with @main suffix
  const mainAtFilename = kokaModuleToFilename(moduleName) + '__main.mjs';

  const mainUrl = moduleUrls.get(mainAtFilename) || moduleUrls.get(mainFilename);
  if (!mainUrl) {
    return `Error: could not find compiled module ${mainFilename}`;
  }

  // Capture output via a DOM element (Koka's browser runtime writes to #koka-console-out)
  const captureEl = document.createElement('div');
  captureEl.id = 'koka-console-out';
  captureEl.style.display = 'none';
  document.body.appendChild(captureEl);

  try {
    // Rewrite imports in all modules to use blob URLs
    // This is a simplified version — for full support, use the playground's module-runner
    const mainModule = await import(/* @vite-ignore */ mainUrl);
    if (typeof mainModule.main === 'function') {
      await mainModule.main();
    } else if (typeof mainModule.default === 'function') {
      await mainModule.default();
    }

    // Read captured output
    const output = captureEl.innerHTML
      .replace(/<br\s*\/?>/g, '\n')
      .replace(/<[^>]+>/g, '')
      .trim();

    return output;
  } finally {
    captureEl.remove();
    // Revoke blob URLs
    for (const url of moduleUrls.values()) {
      URL.revokeObjectURL(url);
    }
  }
}
