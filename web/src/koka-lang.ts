/**
 * koka-lang.ts
 *
 * Monaco language definition for Koka syntax highlighting.
 * Registers the language "koka" and provides:
 *   - tokenisation rules (keywords, types, literals, comments, operators)
 *   - bracket matching configuration
 *   - basic language configuration (comment toggling, auto-close pairs)
 */

import type * as Monaco from 'monaco-editor';

// ── Language identifier ──────────────────────────────────────────────────────

export const KOKA_LANGUAGE_ID = 'koka';

// ── Keyword sets ─────────────────────────────────────────────────────────────

const KEYWORDS: string[] = [
  'fun', 'val', 'var', 'type', 'effect', 'handler', 'handle',
  'match', 'if', 'then', 'else', 'return', 'module', 'import',
  'pub', 'abstract', 'extern', 'with', 'fn', 'forall', 'exists',
  'some', 'struct', 'con', 'alias', 'open', 'extend', 'linear',
  'ref', 'named', 'scoped', 'initially', 'finally', 'raw',
  'ctl', 'final', 'override', 'interface', 'instance',
  'inline', 'noinline', 'tail', 'rec', 'in', 'yield',
  'resume', 'mask', 'inject', 'behind', 'fip', 'fbip',
];

// ── Registration ─────────────────────────────────────────────────────────────

export function registerKokaLanguage(monaco: typeof Monaco): void {
  // Guard against double registration
  const existing = monaco.languages.getLanguages().find(
    (l) => l.id === KOKA_LANGUAGE_ID,
  );
  if (existing) return;

  monaco.languages.register({
    id: KOKA_LANGUAGE_ID,
    extensions: ['.kk', '.kki'],
    aliases: ['Koka', 'koka'],
    mimetypes: ['text/x-koka'],
  });

  // ── Language configuration (bracket pairs, comment commands) ──────────────
  monaco.languages.setLanguageConfiguration(KOKA_LANGUAGE_ID, {
    comments: {
      lineComment: '//',
      blockComment: ['/*', '*/'],
    },
    brackets: [
      ['{', '}'],
      ['[', ']'],
      ['(', ')'],
    ],
    autoClosingPairs: [
      { open: '{', close: '}' },
      { open: '[', close: ']' },
      { open: '(', close: ')' },
      { open: '"', close: '"', notIn: ['string', 'comment'] },
      { open: "'", close: "'", notIn: ['string', 'comment'] },
    ],
    surroundingPairs: [
      { open: '{', close: '}' },
      { open: '[', close: ']' },
      { open: '(', close: ')' },
      { open: '"', close: '"' },
      { open: "'", close: "'" },
    ],
    indentationRules: {
      // Increase indent after lines ending with =, ->, then, else, do
      increaseIndentPattern: /^\s*(fun|if|then|else|match|handler|handle|with|do)\b.*$/,
      decreaseIndentPattern: /^\s*[}\])].*$/,
    },
    folding: {
      markers: {
        start: /^\s*\/\*\*/,
        end:   /^\s*\*\//,
      },
    },
  });

  // ── Monarch tokenizer ──────────────────────────────────────────────────────
  monaco.languages.setMonarchTokensProvider(KOKA_LANGUAGE_ID, {
    keywords: KEYWORDS,

    // Type identifiers start with upper-case
    typeIdent: /[A-Z][a-zA-Z0-9_-]*/,

    // Operators (Koka is operator-rich)
    operators: [
      '=', '->', '=>', '::', ':', '.', '|', '\\', '?', '!',
      '+', '-', '*', '/', '%', '<', '>', '<=', '>=', '==', '!=',
      '&&', '||', '++', '~', '^^', '&', '<<', '>>',
    ],

    tokenizer: {
      root: [
        // Whitespace
        [/[ \t\r\n]+/, 'white'],

        // Block comments (nested-aware via state push)
        [/\/\*/, 'comment', '@blockComment'],

        // Line comments
        [/\/\/.*$/, 'comment'],

        // String literals (double-quoted, with escape sequences)
        [/"/, 'string', '@string'],

        // Raw strings  @"..."  (Koka raw string syntax)
        [/@"/, 'string', '@rawString'],

        // Character literals
        [/'[^'\\]'/, 'string'],
        [/'\\.'/, 'string'],

        // Numbers: hex, float, int
        [/0[xX][0-9a-fA-F]+/, 'number.hex'],
        [/\d+\.\d+([eE][+-]?\d+)?/, 'number.float'],
        [/\d+/, 'number'],

        // Type identifiers (Capitalised)
        [/[A-Z][a-zA-Z0-9_-]*/, 'type.identifier'],

        // Identifiers / keywords
        [
          /[a-z_][a-zA-Z0-9_-]*/,
          {
            cases: {
              '@keywords': 'keyword',
              '@default':  'identifier',
            },
          },
        ],

        // Operators
        [/[=\-><|\\?!+*\/%&~^:]+/, 'operator'],

        // Punctuation / brackets
        [/[{}[\]()]/, '@brackets'],
        [/[,;.]/, 'delimiter'],
      ],

      // ── Double-quoted strings ─────────────────────────────────────────────
      string: [
        [/[^"\\]+/, 'string'],
        [/\\./, 'string.escape'],
        [/"/, 'string', '@pop'],
      ],

      // ── Raw strings @"..." ────────────────────────────────────────────────
      rawString: [
        [/[^"]+/, 'string'],
        [/"/, 'string', '@pop'],
      ],

      // ── Block comments (allow one level of nesting) ───────────────────────
      blockComment: [
        [/[^/*]+/, 'comment'],
        [/\/\*/, 'comment', '@push'],
        [/\*\//, 'comment', '@pop'],
        [/[/*]/, 'comment'],
      ],
    },
  });

  // ── Completion provider (minimal: keyword snippets) ───────────────────────
  monaco.languages.registerCompletionItemProvider(KOKA_LANGUAGE_ID, {
    provideCompletionItems(model, position) {
      const word = model.getWordUntilPosition(position);
      const range: Monaco.IRange = {
        startLineNumber: position.lineNumber,
        endLineNumber:   position.lineNumber,
        startColumn:     word.startColumn,
        endColumn:       word.endColumn,
      };

      const suggestions: Monaco.languages.CompletionItem[] = [
        // Snippet: fun
        {
          label: 'fun',
          kind:  monaco.languages.CompletionItemKind.Snippet,
          insertText: 'fun ${1:name}(${2:args})\n  ${3:body}',
          insertTextRules:
            monaco.languages.CompletionItemInsertTextRule.InsertAsSnippet,
          documentation: 'Define a function',
          range,
        },
        // Snippet: match
        {
          label: 'match',
          kind:  monaco.languages.CompletionItemKind.Snippet,
          insertText: 'match ${1:expr}\n  ${2:pattern} -> ${3:result}',
          insertTextRules:
            monaco.languages.CompletionItemInsertTextRule.InsertAsSnippet,
          documentation: 'Pattern match expression',
          range,
        },
        // Snippet: effect + handler
        {
          label: 'effect',
          kind:  monaco.languages.CompletionItemKind.Snippet,
          insertText:
            'effect ${1:Name}\n  ctl ${2:op}(${3:args}) : ${4:result}',
          insertTextRules:
            monaco.languages.CompletionItemInsertTextRule.InsertAsSnippet,
          documentation: 'Declare an algebraic effect',
          range,
        },
        // Plain keywords
        ...KEYWORDS.map((kw) => ({
          label: kw,
          kind:  monaco.languages.CompletionItemKind.Keyword,
          insertText: kw,
          range,
        })),
      ];

      return { suggestions };
    },
  });
}
