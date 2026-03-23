/**
 * lsp-client.ts
 *
 * Connects Monaco to the Koka WASM LSP server running in a Web Worker.
 * Uses SharedArrayBuffer + Atomics for stdin delivery, and postMessage
 * for stdout (response) retrieval.
 *
 * The LSP server uses Content-Length framed JSON-RPC over stdio.
 * This module:
 *   - Creates the worker and initializes the WASM LSP
 *   - Bridges vscode-jsonrpc MessageReader/MessageWriter to the worker
 *   - Creates a MonacoLanguageClient connected to the transport
 */

import {
  AbstractMessageReader,
  AbstractMessageWriter,
  type DataCallback,
  type Message,
  type Disposable,
  type MessageReader,
  type MessageWriter,
} from 'vscode-jsonrpc/browser.js';
import { MonacoLanguageClient } from 'monaco-languageclient';
import { ExecuteCommandRequest } from 'vscode-languageclient/browser.js';
import type { KokaVFS } from './vfs';

// ── Message Reader (worker stdout → client) ─────────────────────────────────

class WorkerMessageReader extends AbstractMessageReader implements MessageReader {
  private callback: DataCallback | null = null;
  private readonly worker: Worker;

  constructor(worker: Worker) {
    super();
    this.worker = worker;
    this.worker.addEventListener('message', (e: MessageEvent) => {
      if (e.data.type === 'response' && this.callback) {
        try {
          const msg = JSON.parse(e.data.data) as Message;
          this.callback(msg);
        } catch (err) {
          this.fireError(err as Error);
        }
      }
    });
  }

  listen(callback: DataCallback): Disposable {
    this.callback = callback;
    return {
      dispose: () => { this.callback = null; },
    };
  }
}

// ── Message Writer (client → worker stdin via SharedArrayBuffer) ─────────────

class WorkerMessageWriter extends AbstractMessageWriter implements MessageWriter {
  private flagView: Int32Array | null = null;
  private sharedBuffer: SharedArrayBuffer | null = null;
  private readonly encoder = new TextEncoder();

  setSharedBuffer(sharedBuffer: SharedArrayBuffer): void {
    this.sharedBuffer = sharedBuffer;
    this.flagView = new Int32Array(sharedBuffer, 0, 2);
  }

  async write(msg: Message): Promise<void> {
    if (!this.sharedBuffer || !this.flagView) {
      throw new Error('SharedArrayBuffer not initialized');
    }

    const json = JSON.stringify(msg);
    const body = this.encoder.encode(json);
    const header = this.encoder.encode(`Content-Length: ${body.byteLength}\r\n\r\n`);

    const totalLen = header.byteLength + body.byteLength;

    // Wait until the worker has consumed the previous message
    while (Atomics.load(this.flagView, 0) !== 0) {
      // Spin briefly — the worker should consume quickly
      await new Promise(r => setTimeout(r, 1));
    }

    // Write the full LSP message (header + body) into the shared buffer
    const dataView = new Uint8Array(this.sharedBuffer, 8);
    dataView.set(header, 0);
    dataView.set(body, header.byteLength);

    // Set length and signal data ready
    Atomics.store(this.flagView, 1, totalLen);
    Atomics.store(this.flagView, 0, 1);
    Atomics.notify(this.flagView, 0);
  }

  end(): void {
    // Nothing to clean up
  }
}

// ── Public API ──────────────────────────────────────────────────────────────

export interface LspClientOptions {
  /** URL to the koka-lsp.wasm file */
  wasmUrl: string;
  /** The VFS containing stdlib sources and precompiled files */
  vfs: KokaVFS;
  /** Called for LSP server log messages (stderr) */
  onLog?: (text: string) => void;
}

/**
 * Start the WASM LSP server in a Web Worker and connect MonacoLanguageClient.
 * Returns the client instance (already started).
 */
export async function startLspClient(
  options: LspClientOptions,
): Promise<MonacoLanguageClient> {
  // Check for SharedArrayBuffer support
  if (typeof SharedArrayBuffer === 'undefined') {
    throw new Error(
      'SharedArrayBuffer not available. The page must be served with ' +
      'Cross-Origin-Opener-Policy: same-origin and ' +
      'Cross-Origin-Embedder-Policy: require-corp headers.'
    );
  }

  const worker = new Worker(
    new URL('./lsp-worker.ts', import.meta.url),
    { type: 'module' },
  );

  // Collect VFS files for the LSP server's filesystem
  const vfsFiles = options.vfs.getAllFiles();

  // Set up reader and writer
  const reader = new WorkerMessageReader(worker);
  const writer = new WorkerMessageWriter();

  // Forward log messages
  worker.addEventListener('message', (e: MessageEvent) => {
    if (e.data.type === 'log' && options.onLog) {
      options.onLog(e.data.text);
    }
    if (e.data.type === 'error') {
      console.error('[LSP Worker Error]', e.data.message);
    }
  });

  // Initialize: send WASM URL and files, wait for ready + shared buffer
  await new Promise<void>((resolve, reject) => {
    const handler = (e: MessageEvent) => {
      if (e.data.type === 'ready') {
        writer.setSharedBuffer(e.data.sharedBuffer);
        worker.removeEventListener('message', handler);
        resolve();
      } else if (e.data.type === 'error') {
        worker.removeEventListener('message', handler);
        reject(new Error(e.data.message));
      }
    };
    worker.addEventListener('message', handler);
    worker.postMessage({
      type: 'init',
      wasmUrl: options.wasmUrl,
      files: Array.from(vfsFiles.entries()),
    });
  });

  // initServices() must have been called before this point (in main.ts)
  const client = new MonacoLanguageClient({
    name: 'Koka Language Server',
    clientOptions: {
      documentSelector: [{ language: 'koka' }],
      markdown: {
        isTrusted: true,
        supportHtml: true,
      },
      middleware: {
        executeCommand: async (command: string, args: unknown[], next: (...a: unknown[]) => unknown) => {
          if (command === 'koka/signature-help/set-context') {
            // Set context on the backend, then trigger Monaco's parameter hints
            await next(command, args);
            // Trigger signature help in Monaco
            const editor = (await import('@codingame/monaco-vscode-editor-api')).editor;
            const activeEditor = editor.getEditors()[0];
            if (activeEditor) {
              activeEditor.trigger('koka', 'editor.action.triggerParameterHints', {});
            }
          } else {
            return next(command, args);
          }
        },
      },
    },
    messageTransports: { reader, writer },
  });

  await client.start();

  // Send dark/light theme to the LSP server for colored markdown
  try {
    const isDark = document.body.classList.contains('vscode-dark') ||
                   window.matchMedia('(prefers-color-scheme: dark)').matches;
    await client.sendRequest(ExecuteCommandRequest.type, {
      command: 'koka/set-colors',
      arguments: [{ mode: isDark ? 'dark' : 'light' }],
    });
  } catch {
    // koka/set-colors is optional — ignore errors
  }

  return client;
}
