/**
 * wasm-worker.ts
 *
 * Web Worker that runs the WASM Koka compiler off the main thread.
 * Communicates via postMessage:
 *
 * Main → Worker:
 *   { type: 'init', wasmUrl: string }
 *   { type: 'compile', moduleName: string, sourceText: string, files: [path, content][] }
 *
 * Worker → Main:
 *   { type: 'ready' }
 *   { type: 'log', text: string }
 *   { type: 'result', success: boolean, stdout: string, stderr: string, generatedFiles: [path, content][] }
 *   { type: 'error', message: string }
 */

import {
  WASI,
  File,
  OpenFile,
  Directory,
  PreopenDirectory,
  ConsoleStdout,
} from '@bjorn3/browser_wasi_shim';

let wasmModule: WebAssembly.Module | null = null;

self.onmessage = async (e: MessageEvent) => {
  const msg = e.data;

  if (msg.type === 'init') {
    try {
      const response = await fetch(msg.wasmUrl);
      const bytes = await response.arrayBuffer();
      wasmModule = await WebAssembly.compile(bytes);
      self.postMessage({ type: 'ready' });
    } catch (err) {
      self.postMessage({ type: 'error', message: String(err) });
    }
    return;
  }

  if (msg.type === 'compile') {
    if (!wasmModule) {
      self.postMessage({ type: 'error', message: 'WASM module not loaded' });
      return;
    }

    try {
      const allFiles = new Map<string, string>(msg.files);
      const result = runCompiler(wasmModule, msg.moduleName, msg.sourceText, allFiles);
      self.postMessage({
        type: 'result',
        success: result.success,
        stdout: result.stdout,
        stderr: result.stderr,
        generatedFiles: Array.from(result.generatedFiles.entries()),
      });
    } catch (err) {
      self.postMessage({ type: 'error', message: String(err) });
    }
    return;
  }
};

function runCompiler(
  module: WebAssembly.Module,
  moduleName: string,
  sourceText: string,
  allFiles: Map<string, string>,
): { success: boolean; stdout: string; stderr: string; generatedFiles: Map<string, string> } {
  // Build WASI filesystem
  const shareLibFiles = new Map<string, string>();
  const libFiles = new Map<string, string>();
  const rootFiles = new Map<string, string>();

  for (const [path, content] of allFiles) {
    if (path.startsWith('/share/lib/')) {
      shareLibFiles.set(path.slice('/share/lib/'.length), content);
    } else if (path.startsWith('/lib/')) {
      libFiles.set(path.slice('/lib/'.length), content);
    } else if (path.startsWith('/.koka')) {
      // skip previous output
    } else {
      rootFiles.set(path.slice(1), content);
    }
  }

  const shareLibDir = buildDirectoryTree(shareLibFiles);
  const libDir = buildDirectoryTree(libFiles);
  const rootDir = buildDirectoryTree(rootFiles);
  const outputContents = new Map<string, File | Directory>();

  const stdinFile = new File(new TextEncoder().encode(sourceText));

  const stdoutLines: string[] = [];
  const stderrLines: string[] = [];

  const wasi = new WASI(
    ['koka-playground', moduleName],
    [],
    [
      new OpenFile(stdinFile),
      ConsoleStdout.lineBuffered((line) => stdoutLines.push(line)),
      ConsoleStdout.lineBuffered((line) => {
        stderrLines.push(line);
        // Send log lines in real time to the main thread
        self.postMessage({ type: 'log', text: line });
      }),
      new PreopenDirectory('/', rootDir.contents as Map<string, File | Directory>),
      new PreopenDirectory('/share/lib', shareLibDir.contents as Map<string, File | Directory>),
      new PreopenDirectory('/lib', libDir.contents as Map<string, File | Directory>),
      new PreopenDirectory('/.koka', outputContents),
    ],
  );

  const instance = new WebAssembly.Instance(module, {
    wasi_snapshot_preview1: wasi.wasiImport,
  });

  try {
    wasi.start(instance as unknown as { exports: { memory: WebAssembly.Memory; _start: () => void } });
  } catch (e) {
    if (!(e instanceof Error && e.message?.includes('exit'))) {
      stderrLines.push(String(e));
    }
  }

  // Collect output files
  const generatedFiles = new Map<string, string>();
  const decoder = new TextDecoder();
  const outputDirForCollection = new Directory(outputContents);
  collectFilesFromDir(outputDirForCollection, '', generatedFiles, decoder);

  const stdout = stdoutLines.join('\n');
  const stderr = stderrLines.join('\n');

  let success = false;
  try {
    const result = JSON.parse(stdout);
    success = result.success === true;
  } catch { /* */ }

  return { success, stdout, stderr, generatedFiles };
}

function buildDirectoryTree(files: Map<string, string>): Directory {
  const root = new Map<string, File | Directory>();

  for (const [path, content] of files) {
    const parts = path.split('/').filter(Boolean);
    let current = root;

    for (let i = 0; i < parts.length - 1; i++) {
      const part = parts[i];
      if (!current.has(part)) {
        current.set(part, new Directory(new Map()));
      }
      const dir = current.get(part);
      if (dir instanceof Directory) {
        current = dir.contents as Map<string, File | Directory>;
      }
    }

    const filename = parts[parts.length - 1];
    if (filename) {
      current.set(filename, new File(new TextEncoder().encode(content)));
    }
  }

  return new Directory(root);
}

function collectFilesFromDir(
  dir: Directory, prefix: string,
  out: Map<string, string>, decoder: TextDecoder,
): void {
  for (const [name, entry] of dir.contents) {
    const path = prefix ? prefix + '/' + name : name;
    if (entry instanceof File) {
      out.set(path, decoder.decode(entry.data));
    } else if (entry instanceof Directory) {
      collectFilesFromDir(entry, path, out, decoder);
    }
  }
}
