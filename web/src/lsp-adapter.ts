/**
 * lsp-adapter.ts
 *
 * Adapts between Monaco's language features API and the Koka compiler's
 * analysis functions exposed via globalThis.
 *
 * Instead of running a full LSP server, we call individual Haskell functions
 * directly and convert their results to Monaco's expected formats.
 *
 * The service object is populated by the Haskell/GHCJS compiler bundle when it
 * initialises.  Until those functions are available, all providers return
 * empty / null results so the editor stays functional.
 *
 * Usage:
 *   import { registerLanguageProviders } from './lsp-adapter';
 *
 *   const service: KokaLanguageService = {};
 *   registerLanguageProviders(monaco, 'koka', service);
 *
 *   // Later, when the compiler loads:
 *   service.hover = async (file, line, col) => { ... };
 */

// ── Public result types ───────────────────────────────────────────────────────

export interface HoverResult {
  /** Markdown-formatted hover content */
  contents: string;
  range?: { startLine: number; startCol: number; endLine: number; endCol: number };
}

export interface CompletionResult {
  label: string;
  kind: 'function' | 'variable' | 'type' | 'keyword' | 'module' | 'constructor';
  detail?: string;
  documentation?: string;
  insertText?: string;
}

export interface DiagnosticResult {
  severity: 'error' | 'warning' | 'info' | 'hint';
  message: string;
  range: { startLine: number; startCol: number; endLine: number; endCol: number };
}

export interface LocationResult {
  file: string;
  line: number;
  col: number;
}

export interface SymbolResult {
  name: string;
  kind: 'function' | 'variable' | 'type' | 'module' | 'constructor';
  range: { startLine: number; startCol: number; endLine: number; endCol: number };
  children?: SymbolResult[];
}

// ── Service interface ─────────────────────────────────────────────────────────

/**
 * The language service object is a mutable bag of optional functions.
 * The Haskell compiler bundle populates it at runtime; all fields start
 * undefined so providers degrade gracefully.
 */
export interface KokaLanguageService {
  hover?:          (file: string, line: number, col: number) => Promise<HoverResult | null>;
  complete?:       (file: string, line: number, col: number) => Promise<CompletionResult[]>;
  diagnostics?:    (file: string, content: string)           => Promise<DiagnosticResult[]>;
  definition?:     (file: string, line: number, col: number) => Promise<LocationResult | null>;
  documentSymbols?:(file: string)                            => Promise<SymbolResult[]>;
}

// ── Monaco provider registration ─────────────────────────────────────────────

/**
 * Register Monaco language feature providers that delegate to the Koka
 * compiler's analysis functions when available.
 *
 * @param monacoInstance  The imported `monaco-editor` namespace.
 * @param languageId      Language ID to attach providers to (e.g. `'koka'`).
 * @param service         Mutable service object; populate its fields later
 *                        when the compiler bundle loads.
 */
export function registerLanguageProviders(
  monacoInstance: typeof import('monaco-editor'),
  languageId: string,
  service: KokaLanguageService,
): void {

  // ── Hover provider ────────────────────────────────────────────────────────
  monacoInstance.languages.registerHoverProvider(languageId, {
    async provideHover(model, position) {
      if (!service.hover) return null;

      const file   = model.uri.path;
      const result = await service.hover(file, position.lineNumber, position.column);
      if (!result) return null;

      return {
        contents: [{ value: result.contents }],
        range: result.range
          ? new monacoInstance.Range(
              result.range.startLine, result.range.startCol,
              result.range.endLine,   result.range.endCol,
            )
          : undefined,
      };
    },
  });

  // ── Completion provider ───────────────────────────────────────────────────
  monacoInstance.languages.registerCompletionItemProvider(languageId, {
    triggerCharacters: ['.', ':', '/', ' '],

    async provideCompletionItems(model, position) {
      if (!service.complete) return { suggestions: [] };

      const file    = model.uri.path;
      const results = await service.complete(file, position.lineNumber, position.column);

      const word  = model.getWordUntilPosition(position);
      const range = {
        startLineNumber: position.lineNumber,
        endLineNumber:   position.lineNumber,
        startColumn:     word.startColumn,
        endColumn:       word.endColumn,
      };

      const kindMap: Record<CompletionResult['kind'], number> = {
        function:    monacoInstance.languages.CompletionItemKind.Function,
        variable:    monacoInstance.languages.CompletionItemKind.Variable,
        type:        monacoInstance.languages.CompletionItemKind.Class,
        keyword:     monacoInstance.languages.CompletionItemKind.Keyword,
        module:      monacoInstance.languages.CompletionItemKind.Module,
        constructor: monacoInstance.languages.CompletionItemKind.Constructor,
      };

      return {
        suggestions: results.map((r) => ({
          label:         r.label,
          kind:          kindMap[r.kind] ?? monacoInstance.languages.CompletionItemKind.Text,
          detail:        r.detail,
          documentation: r.documentation ? { value: r.documentation } : undefined,
          insertText:    r.insertText ?? r.label,
          range,
        })),
      };
    },
  });

  // ── Definition provider ───────────────────────────────────────────────────
  monacoInstance.languages.registerDefinitionProvider(languageId, {
    async provideDefinition(model, position) {
      if (!service.definition) return null;

      const file   = model.uri.path;
      const result = await service.definition(file, position.lineNumber, position.column);
      if (!result) return null;

      return {
        uri:   monacoInstance.Uri.file(result.file),
        range: new monacoInstance.Range(result.line, result.col, result.line, result.col),
      };
    },
  });

  // ── Document symbols provider ─────────────────────────────────────────────
  monacoInstance.languages.registerDocumentSymbolProvider(languageId, {
    async provideDocumentSymbols(model) {
      if (!service.documentSymbols) return [];

      const file    = model.uri.path;
      const symbols = await service.documentSymbols(file);

      return convertSymbols(monacoInstance, symbols);
    },
  });

  // ── Diagnostics (markers) — poll-based ───────────────────────────────────
  //
  // There is no push mechanism yet.  The compile function already produces
  // diagnostics; call `applyDiagnostics` after each compilation to display
  // them as squiggles in the editor.
}

// ── Diagnostics helper ────────────────────────────────────────────────────────

/** Severity map from KokaLanguageService to Monaco's MarkerSeverity */
const SEVERITY_MAP = {
  error:   8, // monaco.MarkerSeverity.Error
  warning: 4, // monaco.MarkerSeverity.Warning
  info:    2, // monaco.MarkerSeverity.Info
  hint:    1, // monaco.MarkerSeverity.Hint
} as const;

/**
 * Convert DiagnosticResult[] into Monaco editor markers and apply them to the
 * model identified by `uri`.
 *
 * Call this after each compilation to display errors and warnings as
 * squiggly underlines in the editor.
 *
 * @param monacoInstance  The imported `monaco-editor` namespace.
 * @param uri             URI of the model to annotate.
 * @param diagnostics     Diagnostics from the compiler.
 */
export function applyDiagnostics(
  monacoInstance: typeof import('monaco-editor'),
  uri: import('monaco-editor').Uri,
  diagnostics: DiagnosticResult[],
): void {
  const model = monacoInstance.editor.getModel(uri);
  if (!model) return;

  const markers: import('monaco-editor').editor.IMarkerData[] = diagnostics.map((d) => ({
    severity: SEVERITY_MAP[d.severity] ?? SEVERITY_MAP.error,
    message:  d.message,
    startLineNumber: d.range.startLine,
    startColumn:     d.range.startCol,
    endLineNumber:   d.range.endLine,
    endColumn:       d.range.endCol,
  }));

  monacoInstance.editor.setModelMarkers(model, 'koka', markers);
}

// ── Internal helpers ──────────────────────────────────────────────────────────

function symbolKindToMonaco(
  monacoInstance: typeof import('monaco-editor'),
  kind: SymbolResult['kind'],
): number {
  // monaco.languages.SymbolKind values
  const map: Record<SymbolResult['kind'], number> = {
    module:      1,
    function:    11,
    variable:    12,
    constructor: 8,
    type:        4,
  };
  return map[kind] ?? 12;
}

function convertSymbols(
  monacoInstance: typeof import('monaco-editor'),
  symbols: SymbolResult[],
): import('monaco-editor').languages.DocumentSymbol[] {
  return symbols.map((s) => ({
    name:           s.name,
    detail:         '',
    kind:           symbolKindToMonaco(monacoInstance, s.kind),
    tags:           [],
    range: new monacoInstance.Range(
      s.range.startLine, s.range.startCol,
      s.range.endLine,   s.range.endCol,
    ),
    selectionRange: new monacoInstance.Range(
      s.range.startLine, s.range.startCol,
      s.range.startLine, s.range.startCol + s.name.length,
    ),
    children: s.children ? convertSymbols(monacoInstance, s.children) : [],
  }));
}
