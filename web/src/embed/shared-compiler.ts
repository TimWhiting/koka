/**
 * shared-compiler.ts
 *
 * Manages a single WASM compiler Web Worker shared by all <koka-editor> elements
 * on the page. Lazily loaded on first compile request.
 */

import { createWasmCompiler, type WasmCompileResult } from '../wasm-runner';

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

// Stdlib data cached after first load
let stdlibSources: Map<string, string> | null = null;
let precompiledFiles: Map<string, string> | null = null;

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
    const wasmUrl = findWasmUrl();
    const stdlibUrl = findStdlibUrl();

    // Load stdlib sources and precompiled files
    const { sources, precompiled } = await loadStdlib(stdlibUrl);
    stdlibSources = sources;
    precompiledFiles = precompiled;

    // Build VFS from stdlib
    const vfsFiles = new Map<string, string>();
    for (const [path, content] of sources) {
      vfsFiles.set('/share/lib/' + path, content);
    }
    for (const [f, content] of precompiled) {
      vfsFiles.set('/lib/js-debug/' + f, content);
    }

    // Create WASM compiler in a Web Worker via wasm-runner
    const compileFn = await createWasmCompiler({
      wasmUrl,
      getAllFiles: () => vfsFiles,
      onLog: (text) => console.log('[koka]', text),
    });

    return {
      compile: async (moduleName, sourceText) => {
        // Add user source to VFS temporarily
        const userPath = '/' + moduleName.replace(/\./g, '/') + '.kk';
        vfsFiles.set(userPath, sourceText);

        const result = await compileFn(moduleName, sourceText);

        // Clean up user source
        vfsFiles.delete(userPath);

        return {
          success: result.success,
          stdout: result.stdout,
          stderr: result.stderr,
          generatedFiles: result.generatedFiles,
        };
      },
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
  const meta = document.querySelector('meta[name="koka-wasm-url"]');
  if (meta) return meta.getAttribute('content') || '';

  const cfg = (globalThis as Record<string, unknown>).kokaConfig as Record<string, string> | undefined;
  if (cfg?.wasmUrl) return cfg.wasmUrl;

  return new URL('koka-playground.wasm', window.location.href).href;
}

function findStdlibUrl(): string {
  const meta = document.querySelector('meta[name="koka-stdlib-url"]');
  if (meta) return meta.getAttribute('content') || '';

  const cfg = (globalThis as Record<string, unknown>).kokaConfig as Record<string, string> | undefined;
  if (cfg?.stdlibUrl) return cfg.stdlibUrl;

  return '';
}

// ── Stdlib loading ──────────────────────────────────────────────────────────

async function loadStdlib(baseUrl: string): Promise<{
  sources: Map<string, string>;
  precompiled: Map<string, string>;
}> {
  const sources = new Map<string, string>();
  const precompiled = new Map<string, string>();
  const prefix = baseUrl ? baseUrl.replace(/\/$/, '') + '/' : '';

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
  const moduleUrls = new Map<string, string>();

  // Add precompiled .mjs
  for (const [name, content] of precompiled) {
    if (name.endsWith('.mjs')) {
      const blob = new Blob([content], { type: 'application/javascript' });
      moduleUrls.set(name, URL.createObjectURL(blob));
    }
  }

  // Add generated .mjs (override precompiled)
  for (const [path, content] of generatedFiles) {
    if (path.endsWith('.mjs')) {
      const name = path.split('/').pop()!;
      const blob = new Blob([content], { type: 'application/javascript' });
      moduleUrls.set(name, URL.createObjectURL(blob));
    }
  }

  const mainFilename = kokaModuleToFilename(moduleName) + '.mjs';
  const mainAtFilename = kokaModuleToFilename(moduleName) + '__main.mjs';
  const mainUrl = moduleUrls.get(mainAtFilename) || moduleUrls.get(mainFilename);

  if (!mainUrl) {
    return `Error: could not find compiled module ${mainFilename}`;
  }

  // Capture output via #koka-console-out
  const captureEl = document.createElement('div');
  captureEl.id = 'koka-console-out';
  captureEl.style.display = 'none';
  document.body.appendChild(captureEl);

  try {
    const mainModule = await import(/* @vite-ignore */ mainUrl);
    if (typeof mainModule.main === 'function') {
      await mainModule.main();
    } else if (typeof mainModule.default === 'function') {
      await mainModule.default();
    }

    return captureEl.innerHTML
      .replace(/<br\s*\/?>/g, '\n')
      .replace(/<[^>]+>/g, '')
      .trim();
  } finally {
    captureEl.remove();
    for (const url of moduleUrls.values()) URL.revokeObjectURL(url);
  }
}
