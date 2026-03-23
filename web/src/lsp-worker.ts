/**
 * lsp-worker.ts
 *
 * Web Worker that runs the Koka LSP server (WASM) off the main thread.
 * Uses SharedArrayBuffer + Atomics for blocking stdin reads.
 *
 * Main → Worker:
 *   { type: 'init', wasmUrl: string, files: [path, content][] }
 *   { type: 'request', data: string }   // raw LSP JSON-RPC message (no headers)
 *
 * Worker → Main:
 *   { type: 'ready' }
 *   { type: 'response', data: string }  // raw LSP JSON-RPC message (no headers)
 *   { type: 'log', text: string }
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

// ── Blocking stdin via SharedArrayBuffer ────────────────────────────────────

/**
 * A custom File-like object for WASI stdin that blocks via Atomics.wait
 * until the main thread sends data.
 *
 * SharedArrayBuffer layout:
 *   Int32[0] = flag (0 = empty, 1 = data ready)
 *   Int32[1] = data length in bytes
 *   Uint8[8..] = data bytes
 */
class BlockingStdinFile {
  private flagView: Int32Array;
  private sharedBuffer: SharedArrayBuffer;
  private pendingData: Uint8Array = new Uint8Array(0);
  private offset = 0;

  constructor(sharedBuffer: SharedArrayBuffer) {
    this.sharedBuffer = sharedBuffer;
    this.flagView = new Int32Array(sharedBuffer, 0, 2);
  }

  fd_read(len: number): { ret: number; data: Uint8Array } {
    // If we have leftover data from a previous read, return that first
    if (this.offset < this.pendingData.length) {
      const available = this.pendingData.length - this.offset;
      const toRead = Math.min(len, available);
      const data = this.pendingData.slice(this.offset, this.offset + toRead);
      this.offset += toRead;
      this.hasReadData = true;
      return { ret: 0, data };
    }

    // Check if new data is available (non-blocking first)
    let flag = Atomics.load(this.flagView, 0);
    if (flag !== 1) {
      // No data right now. Block with a short timeout so the GHC RTS
      // scheduler can run other green threads (e.g. sendServer writing
      // responses to stdout). If no data arrives within the timeout,
      // return empty — hGetSome in Haskell treats empty as "no data yet"
      // and the attoparsec Partial continuation can finalize the parse.
      // The LSP ioLoop will then call hGetSome again for the next message.
      Atomics.wait(this.flagView, 0, 0, 10);
      flag = Atomics.load(this.flagView, 0);
      if (flag !== 1) {
        // Still no data — return empty. The Haskell BS.hGetSome handles
        // this by having the GHC RTS retry (it doesn't treat it as EOF
        // when the handle is still open and non-blocking IO is in effect).
        return { ret: 0, data: new Uint8Array(0) };
      }
    }

    // Data available — read it
    const dataLen = Atomics.load(this.flagView, 1);
    const dataView = new Uint8Array(this.sharedBuffer, 8, dataLen);
    this.pendingData = new Uint8Array(dataView);
    this.offset = 0;

    Atomics.store(this.flagView, 0, 0);
    Atomics.notify(this.flagView, 0);

    const toRead = Math.min(len, this.pendingData.length);
    const data = this.pendingData.slice(0, toRead);
    this.offset = toRead;
    return { ret: 0, data };
  }

  // Required WASI fd interface stubs
  fd_fdstat_get() {
    return { ret: 0, fdstat: null };
  }
  fd_close() { return 0; }
  fd_seek(_offset: bigint, _whence: number) { return { ret: 8, offset: 0n }; }
  fd_tell() { return { ret: 0, offset: 0n }; }
  fd_sync() { return 0; }
  fd_filestat_get() { return { ret: 0, filestat: null }; }
  fd_write(_data: Uint8Array) { return { ret: 8, nwritten: 0 }; }
  fd_pread(_len: number, _offset: bigint) { return { ret: 8, data: new Uint8Array(0) }; }
  fd_pwrite(_data: Uint8Array, _offset: bigint) { return { ret: 8, nwritten: 0 }; }
  fd_allocate(_offset: bigint, _len: bigint) { return 0; }
  fd_fdstat_set_flags(_flags: number) { return 0; }
  fd_fdstat_set_rights(_base: bigint, _inheriting: bigint) { return 0; }
  fd_filestat_set_size(_size: bigint) { return 0; }
  fd_filestat_set_times(_a: bigint, _m: bigint, _flags: number) { return 0; }
  fd_prestat_get() { return { ret: 8, prestat: null }; }
  fd_readdir_single(_cookie: bigint) { return { ret: 8, dirent: null }; }
  path_create_directory(_path: string) { return 8; }
  path_filestat_get(_flags: number, _path: string) { return { ret: 8, filestat: null }; }
  path_filestat_set_times(_f: number, _p: string, _a: bigint, _m: bigint, _fl: number) { return 8; }
  path_lookup(_path: string, _flags: number) { return { ret: 8, inode_obj: null }; }
  path_link(_path: string, _inode: unknown, _force: boolean) { return 8; }
  path_open(..._args: unknown[]) { return { ret: 8, fd_obj: null }; }
  path_readlink(_path: string) { return { ret: 8, data: null }; }
  path_remove_directory(_path: string) { return 8; }
  path_unlink(_path: string) { return { ret: 8, inode_obj: null }; }
  path_unlink_file(_path: string) { return 8; }
}

// ── Stdout capture with LSP message parsing ─────────────────────────────────

/**
 * Captures stdout bytes and parses LSP Content-Length framed messages.
 * Forwards complete JSON-RPC messages back to the main thread via postMessage.
 */
class LspStdoutCapture {
  private buffer = '';
  private readonly decoder = new TextDecoder();

  fd_write(data: Uint8Array): { ret: number; nwritten: number } {
    this.buffer += this.decoder.decode(data, { stream: true });
    this.parseMessages();
    return { ret: 0, nwritten: data.byteLength };
  }

  private parseMessages(): void {
    while (true) {
      // Look for Content-Length header
      const headerEnd = this.buffer.indexOf('\r\n\r\n');
      if (headerEnd === -1) break;

      const headerSection = this.buffer.substring(0, headerEnd);
      const match = headerSection.match(/Content-Length:\s*(\d+)/i);
      if (!match) {
        // Malformed — skip past this header
        this.buffer = this.buffer.substring(headerEnd + 4);
        continue;
      }

      const contentLength = parseInt(match[1], 10);
      const bodyStart = headerEnd + 4;
      const bodyEnd = bodyStart + contentLength;

      if (this.buffer.length < bodyEnd) {
        // Not enough data yet — wait for more
        break;
      }

      const body = this.buffer.substring(bodyStart, bodyEnd);
      this.buffer = this.buffer.substring(bodyEnd);

      // Send parsed JSON-RPC message to main thread
      self.postMessage({ type: 'response', data: body });
    }
  }

  // WASI fd interface
  fd_fdstat_get() { return { ret: 0, fdstat: null }; }
  fd_close() { return 0; }
  fd_seek(_offset: bigint, _whence: number) { return { ret: 8, offset: 0n }; }
  fd_tell() { return { ret: 0, offset: 0n }; }
  fd_sync() { return 0; }
  fd_read(_len: number) { return { ret: 8, data: new Uint8Array(0) }; }
  fd_filestat_get() { return { ret: 0, filestat: null }; }
  fd_pread(_len: number, _offset: bigint) { return { ret: 8, data: new Uint8Array(0) }; }
  fd_pwrite(_data: Uint8Array, _offset: bigint) { return { ret: 8, nwritten: 0 }; }
  fd_allocate(_offset: bigint, _len: bigint) { return 0; }
  fd_fdstat_set_flags(_flags: number) { return 0; }
  fd_fdstat_set_rights(_base: bigint, _inheriting: bigint) { return 0; }
  fd_filestat_set_size(_size: bigint) { return 0; }
  fd_filestat_set_times(_a: bigint, _m: bigint, _flags: number) { return 0; }
  fd_prestat_get() { return { ret: 8, prestat: null }; }
  fd_readdir_single(_cookie: bigint) { return { ret: 8, dirent: null }; }
  path_create_directory(_path: string) { return 8; }
  path_filestat_get(_flags: number, _path: string) { return { ret: 8, filestat: null }; }
  path_filestat_set_times(_f: number, _p: string, _a: bigint, _m: bigint, _fl: number) { return 8; }
  path_lookup(_path: string, _flags: number) { return { ret: 8, inode_obj: null }; }
  path_link(_path: string, _inode: unknown, _force: boolean) { return 8; }
  path_open(..._args: unknown[]) { return { ret: 8, fd_obj: null }; }
  path_readlink(_path: string) { return { ret: 8, data: null }; }
  path_remove_directory(_path: string) { return 8; }
  path_unlink(_path: string) { return { ret: 8, inode_obj: null }; }
  path_unlink_file(_path: string) { return 8; }
}

// ── Shared buffer for stdin communication ───────────────────────────────────

// 1MB shared buffer: [flag:i32, length:i32, data:uint8...]
const SHARED_BUFFER_SIZE = 1024 * 1024;
const sharedBuffer = new SharedArrayBuffer(SHARED_BUFFER_SIZE);
const flagView = new Int32Array(sharedBuffer, 0, 2);

// ── File system builder (reused from wasm-worker) ───────────────────────────

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

// ── Worker message handler ──────────────────────────────────────────────────

let wasmModule: WebAssembly.Module | null = null;

self.onmessage = async (e: MessageEvent) => {
  const msg = e.data;

  if (msg.type === 'init') {
    try {
      // Load and compile WASM module
      const response = await fetch(msg.wasmUrl);
      const bytes = await response.arrayBuffer();
      wasmModule = await WebAssembly.compile(bytes);

      // Build filesystem from provided files
      const allFiles = new Map<string, string>(msg.files);
      const shareLibFiles = new Map<string, string>();
      const libFiles = new Map<string, string>();

      for (const [path, content] of allFiles) {
        if (path.startsWith('/share/lib/')) {
          shareLibFiles.set(path.slice('/share/lib/'.length), content);
        } else if (path.startsWith('/lib/')) {
          libFiles.set(path.slice('/lib/'.length), content);
        }
      }

      const shareLibDir = buildDirectoryTree(shareLibFiles);
      const libDir = buildDirectoryTree(libFiles);
      const rootDir = buildDirectoryTree(new Map());

      // Create blocking stdin and capturing stdout
      const stdinFile = new BlockingStdinFile(sharedBuffer);
      const stdoutCapture = new LspStdoutCapture();

      const wasi = new WASI(
        ['koka-lsp', '--language-server', '--lsstdio', '--sharedir=/share', '--target=js', '--builddir=/lib'],
        [],
        [
          stdinFile as unknown as OpenFile,           // fd 0: stdin
          stdoutCapture as unknown as OpenFile,        // fd 1: stdout
          ConsoleStdout.lineBuffered((line: string) => {
            self.postMessage({ type: 'log', text: line });
          }),                                          // fd 2: stderr
          new PreopenDirectory('/', rootDir.contents as Map<string, File | Directory>),
          new PreopenDirectory('/share/lib', shareLibDir.contents as Map<string, File | Directory>),
          new PreopenDirectory('/lib', libDir.contents as Map<string, File | Directory>),
        ],
        { debug: false },
      );

      // Send the shared buffer to the main thread so it can write to stdin
      self.postMessage({ type: 'ready', sharedBuffer });

      // Start the LSP server (this blocks forever, reading from stdin)
      const instance = new WebAssembly.Instance(wasmModule, {
        wasi_snapshot_preview1: wasi.wasiImport,
      });

      try {
        const result = wasi.start(instance as unknown as { exports: { memory: WebAssembly.Memory; _start: () => void } });
        self.postMessage({ type: 'log', text: `LSP server exited with code ${result}` });
      } catch (err) {
        const msg = err instanceof Error ? err.message : String(err);
        self.postMessage({ type: 'log', text: `LSP server exception: ${msg}` });
        if (!(err instanceof Error && msg.includes('exit'))) {
          self.postMessage({ type: 'error', message: msg });
        }
      }
    } catch (err) {
      self.postMessage({ type: 'error', message: String(err) });
    }
    return;
  }

  // 'request' messages are handled by the main thread writing directly
  // to the SharedArrayBuffer — they don't come through onmessage.
};
