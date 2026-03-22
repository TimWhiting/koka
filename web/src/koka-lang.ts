/**
 * koka-lang.ts
 *
 * Monaco language definition for Koka syntax highlighting.
 *
 * Registers the language "koka" and provides:
 *   - A comprehensive Monarch tokenizer translated from the real TextMate
 *     grammar shipped with the VSCode extension (koka.tmLanguage.json).
 *     This avoids the vscode-oniguruma WASM dependency while still covering
 *     all the important constructs:
 *       · All reserved keywords (incl. modifiers: value, reference, co, lazy, rec)
 *       · Type identifiers, type variables, kind annotations
 *       · Module-qualified identifiers  (foo/bar/baz)
 *       · Raw strings: r"...", r#"..."#, r##"..."##
 *       · Nested block comments
 *       · Effect / handler / ctl keywords with distinct token types
 *       · Declaration keywords (fun, val, var, type, effect, struct, alias)
 *       · Control-flow keywords (if, then, else, elif, match, return)
 *       · Operators including Koka-specific ones (->, =>, ::, :=, <-, |)
 *       · Implicit parameter markers (?) and borrow markers (^)
 *       · Number literals: hex 0x, binary 0b, float with underscore separators
 *         and scientific notation
 *       · Character literals with escape sequences
 *   - Language configuration (brackets, comments, auto-close) from
 *     koka-configuration.json (the VSCode extension's own config).
 *   - A completion provider with keyword snippets.
 */

import type * as Monaco from 'monaco-editor';

// ── Language identifier ──────────────────────────────────────────────────────

export const KOKA_LANGUAGE_ID = 'koka';

// ── Keyword sets (sourced from koka.tmLanguage.json > reservedid / reservedcontrol) ─

/** Reserved keywords that are not control-flow */
const KEYWORDS_RESERVED: string[] = [
  // declaration
  'fun', 'fn', 'val', 'var', 'con', 'extern', 'alias', 'struct',
  // type modifiers / quantifiers
  'type', 'effect', 'ambient', 'linear', 'co', 'rec', 'lazy', 'named', 'scoped',
  'value', 'reference', 'open', 'extend',
  'forall', 'exists', 'some',
  // effects
  'ctl', 'raw', 'final',
  // module system
  'module', 'import', 'as', 'pub', 'abstract', 'in',
  // other
  'with', 'override', 'handle', 'handler',
  'inject', 'mask', 'behind',
  'infix', 'infixr', 'infixl',
  'inline', 'noinline', 'tail',
  'fip', 'fbip',
  'ctx', 'hole',
  'unsafe',
  'break', 'continue',
  'interface', 'instance',
];

/** Control-flow keywords (get a distinct token colour in the TextMate grammar) */
const KEYWORDS_CONTROL: string[] = [
  'if', 'then', 'else', 'elif', 'match', 'return',
];

/** Library identifiers treated as keywords */
const KEYWORDS_LIBRARY: string[] = [
  'resume', 'resume-shallow', 'rcontext',
  'finally', 'initially',
];

const ALL_KEYWORDS: string[] = [
  ...KEYWORDS_RESERVED,
  ...KEYWORDS_CONTROL,
  ...KEYWORDS_LIBRARY,
];

// ── Registration ─────────────────────────────────────────────────────────────

export async function registerKokaLanguage(monaco: typeof Monaco): Promise<void> {
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

  // ── Language configuration (from koka-configuration.json) ─────────────────
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
      { open: '<', close: '>' },
      { open: '"', close: '"', notIn: ['string'] },
      { open: "'", close: "'", notIn: ['string'] },
      { open: '`', close: '`', notIn: ['string'] },
    ],
    surroundingPairs: [
      { open: '{', close: '}' },
      { open: '[', close: ']' },
      { open: '(', close: ')' },
      { open: '<', close: '>' },
      { open: "'", close: "'" },
      { open: '"', close: '"' },
    ],
    indentationRules: {
      increaseIndentPattern: /^\s*(fun|fn|if|then|else|match|handler|handle|with|do)\b.*$/,
      decreaseIndentPattern: /^\s*[}\])].*$/,
    },
    folding: {
      offSide: true,
    },
    wordPattern: /[A-Za-z_]([0-9]|[A-Za-z_\/](\-[A-Za-z_])?)*'*/,
  });

  // ── Comprehensive Monarch tokenizer ───────────────────────────────────────
  //
  // Pattern order matches the TextMate grammar's include order so that more
  // specific patterns shadow less specific ones.
  //
  monaco.languages.setMonarchTokensProvider(KOKA_LANGUAGE_ID, {
    // Keyword tables referenced in token rules via @keywords etc.
    keywords:        KEYWORDS_RESERVED,
    controlKeywords: KEYWORDS_CONTROL,
    libraryKeywords: KEYWORDS_LIBRARY,

    tokenizer: {
      // ── Root (top-level) ───────────────────────────────────────────────
      root: [
        // Whitespace
        [/[ \t\r\n]+/, 'white'],

        // Preprocessor / line directives  (#...)
        [/^\s*#.*$/, 'meta.preprocessor'],

        // Block comments — nested via state push
        [/\/\*/, 'comment.block', '@blockComment'],

        // Line comments (with minimal doc-comment markup)
        [/\/\//, 'comment.line', '@lineComment'],

        // Raw strings (must come before ordinary strings)
        [/r##"/, 'string.raw', '@rawString2'],
        [/r#"/, 'string.raw', '@rawString1'],
        [/r"/, 'string.raw', '@rawString0'],

        // Ordinary strings
        [/"/, 'string', '@string'],

        // Character literals with escape sequences
        [/'(\\([abfnrtvz0\\'"]|x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|U[0-9a-fA-F]{6}))'/, 'string.escape'],
        // Plain character literal (single non-special char)
        [/'[^'\\$]'/, 'string'],

        // Numbers (from koka.tmLanguage.json > number)
        // Hex: 0x... with optional fractional and exponent
        [/0[xX][0-9a-fA-F]+(?:_[0-9a-fA-F]+)*(?:\.[0-9a-fA-F]+(?:_[0-9a-fA-F]+)*)?(?:[pP][+\-]?\d+)?/, 'number.hex'],
        // Binary: 0b...
        [/0[bB][01][01_]*/, 'number.binary'],
        // Decimal / float with optional underscore separators and scientific notation
        [/(?:0|[1-9]\d*)(?:_\d+)*(?:\.\d+(?:_\d+)*(?:[eE][+\-]?\d+)?)?/, 'number'],

        // ── Declaration keywords followed by a name ─────────────────────
        // These patterns mirror the TextMate grammar's decl_* captures so
        // the declared name gets its own token type.

        // fun / fn / ctl / ret + optional module path + name
        [
          /((?:(?:inline|noinline)\s+)?(?:tail\s+)?(?:(?:fip|fbip)(?:\(\d+\))?\s+)?(?:fun|fn|ctl|ret))\s+((?:[a-z@][\w\-]*\/#?)*)([a-z@][\w\-]*'*)/,
          ['keyword.declaration.function', 'entity.name.variable', 'entity.name.function'],
        ],

        // extern + optional module path + name
        [
          /((?:(?:inline|noinline)\s+)?(?:(?:fip|fbip)\s+)?extern)\s+((?:[a-z@][\w\-]*\/#?)*)([a-z@][\w\-]*'*)?/,
          ['keyword.declaration.function', 'entity.name.variable', 'entity.name.function'],
        ],

        // val (top-level or inline) + name
        [
          /((?:(?:inline|noinline)\s+)?val)\s+((?:[a-z@][\w\-]*\/#?)*)([a-z@][\w\-]*'*)?/,
          ['keyword.declaration', 'entity.name.variable', 'entity.name.function'],
        ],

        // var + name
        [
          /(var)\s+([a-z][\w\-]*'*)/,
          ['keyword.declaration', 'entity.name'],
        ],

        // module <path>
        [
          /(module)\s*((interface)?)\s*((?:[a-z][\w\-]*\/)*[a-z][\w\-]*)/,
          ['keyword.other', 'keyword.other', 'keyword.other', 'entity.name.variable'],
        ],

        // import <path> [= <alias>]
        [
          /(import)\s+((?:[a-z][\w\-]*\/)*[a-z][\w\-]*)/,
          ['keyword', 'entity.name.variable'],
        ],

        // type / effect / struct / alias declarations — enter type-annotation state
        [
          /((?:(?:value|reference|open|extend|rec|co|lazy(?:\s+tail)?(?:\s+(?:fip|fbip)(?:\(\d+\))?)?)?)\s*type|(?:named\s+)?(?:scoped\s+)?(?:linear\s+)?(?:rec\s+)?(?:effect|ambient))\s+(?!fn|fun|val|raw|final|ctl|ret)((?:[a-z@][\w\-]*\/#?)*)(@?[a-z][\w\-]*'*)/,
          ['keyword.declaration.type', 'entity.name.variable', 'support.type'],
        ],

        // struct <name>
        [
          /((?:(?:value|ref)\s*)?struct)\s+((?:[a-z@][\w\-]*\/#?)*)(@?[a-z][\w\-]*'*)/,
          ['keyword.declaration', 'entity.name.variable', 'support.type'],
        ],

        // alias <name>
        [
          /(alias)\s+([a-z][\w\-]+)/,
          ['keyword.declaration', 'support.type'],
        ],

        // ── Reserved control flow ───────────────────────────────────────
        [
          /\b(if|then|else|elif|match|return)(?![\w\-'])/,
          'keyword.control',
        ],

        // ── Library identifiers (resume, finally, initially, …) ────────
        [
          /\b(resume(?:-shallow)?|rcontext|finally|initially)(?![\w\-'])/,
          'keyword.control',
        ],

        // ── Extern target specifiers (c, cs, js, inline …) ─────────────
        [
          /\b(?:c|cs|js|inline)\s+(?:inline\s+)?(?:(?:file|header-file|header-end-file)\s+)?(?=["{\r\n]|r#*")/,
          'keyword.control',
        ],

        // ── Type annotation introducer (colon not followed by more operators) ─
        //    Switches into a lightweight inline-type state
        [/(:(?![$%&*+@!\\\^~=.:\-?|<>]))|(\bwhere\b|\biff\b|\bwhen\b)/, { token: 'support.type', next: '@inlineType' }],

        // ── All other reserved keywords ────────────────────────────────
        [
          /\b(return(?=(?:\(|\s+\(?)[\w][\w\-]*\s*(?:\)\s*(?:[^;])))|infix[rl]?|type|co|lazy(?:\s+tail)?(?:\s+(?:fip|fbip)(?:\(\d+\))?)?|rec|struct|alias|forall|exists|some|extern|fun|fn|val|var|con|with(?:\s+override)?|module|import|as|in|ctx|hole|pub|abstract|effect|named|(?:raw\s+|final\s+)?ctl|break|continue|unsafe|mask(?:\s+behind)?|handle|handler|inject|value|reference|open|extend|linear|scoped|named|override|inline|noinline|tail|fip|fbip|interface|instance)(?![\w\-'])/,
          'keyword.other',
        ],

        // ── Module-qualified constructor:  foo/bar/Baz ─────────────────
        [/((?:[a-z@][\w\-]*\/#?)+)(@?[A-Z][\w\-]*'*)/, ['entity.name.variable', 'entity.name.tag']],

        // ── Module-qualified operator:  foo/bar/(++) ───────────────────
        [/((?:[a-z@][\w\-]*\/#?)+)(\([^\n\r)]+\))/, ['entity.name.variable', 'source.operator']],

        // ── Module-qualified identifier:  foo/bar/baz ──────────────────
        [/([?]?(?:[a-z@][\w\-]*\/#?)+)(@?[a-z][\w\-]*'*)/, ['entity.name.variable', 'source']],

        // ── Constructors (start with upper-case) ───────────────────────
        [/@?[A-Z][\w\-]*'*/, 'entity.name.tag'],

        // ── Wildcard ────────────────────────────────────────────────────
        [/@?_[\w\-]*'*/, 'source.wildcard'],

        // ── Plain identifiers ───────────────────────────────────────────
        [/@?[a-z][\w\-]*'*/, 'source'],

        // ── Reserved operators (from reservedop in the grammar) ─────────
        [/(=|=>|->|<-|\||\.+|::|:=)(?![$%&*+!/\\\^~=.:\-?|<>])/, 'keyword'],

        // ── Borrow marker ^ ─────────────────────────────────────────────
        [/\^/, 'keyword.other'],

        // ── Implicit parameter marker ? ─────────────────────────────────
        [/\?/, 'keyword.other'],

        // ── Minus (unary/binary, disambiguated) ─────────────────────────
        [/-(?![$%&*+@!/\\\^~=.:\-?|<>])/, 'source.operator.minus'],

        // ── General operators ────────────────────────────────────────────
        [/[$%&*+@!/\\\^~=.:\-?|<>]+/, 'source.operator'],

        // ── Punctuation ──────────────────────────────────────────────────
        [/[{}()\[\];,]/, 'punctuation.separator'],
      ],

      // ── Line comment (allows rudimentary doc-comment markup) ──────────────
      lineComment: [
        [/`(:[^\`\n]+)`/, { token: 'comment.doc.type', next: '@pop' }],
        [/`(module [^\`\n]+)`/, { token: 'comment.doc.module', next: '@pop' }],
        [/`+([^\`\n]*)`+/, { token: 'comment.doc.source', next: '@pop' }],
        [/$/, { token: 'comment.line', next: '@pop' }],
        [/[^`$\n]+/, 'comment.line'],
        [/./, 'comment.line'],
      ],

      // ── Nested block comment ──────────────────────────────────────────────
      blockComment: [
        [/[^/*]+/, 'comment.block'],
        [/\/\*/, 'comment.block', '@push'],
        [/\*\//, 'comment.block', '@pop'],
        [/[/*]/, 'comment.block'],
      ],

      // ── Ordinary double-quoted string ─────────────────────────────────────
      string: [
        [/[^"\\]+/, 'string'],
        [/\\([abfnrtvz0\\'"\?]|x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|U[0-9a-fA-F]{6})/, 'string.escape'],
        [/\\./, 'string.escape.invalid'],
        [/"/, 'string', '@pop'],
      ],

      // ── Raw strings ───────────────────────────────────────────────────────
      // r"..."  — no escapes, ends at first "
      rawString0: [
        [/[^"]+/, 'string.raw'],
        [/"/, 'string.raw', '@pop'],
      ],

      // r#"..."#  — ends at "#
      rawString1: [
        [/[^"]+/, 'string.raw'],
        [/"(?!#)/, 'string.raw'],
        [/"#/, 'string.raw', '@pop'],
      ],

      // r##"..."##  — ends at "##
      rawString2: [
        [/[^"]+/, 'string.raw'],
        [/"(?!##)/, 'string.raw'],
        [/"##/, 'string.raw', '@pop'],
      ],

      // ── Inline type annotation (after ':' or 'where'/'iff'/'when') ────────
      //
      // We highlight identifiers as type tokens until we hit a delimiter that
      // ends the type context (mirroring the TextMate grammar's top_type rule).
      //
      inlineType: [
        // Whitespace — stay in type state
        [/[ \t]+/, 'support.type'],

        // Type-level comments
        [/\/\*/, 'comment.block', '@blockComment'],
        [/\/\/.*$/, 'comment.line'],

        // Type operators: -> :: : .
        [/(->|::?|\.)(?![$%&*+@!\\\^~=.:\-?|<>])/, 'support.type'],

        // Type keywords
        [/\b(forall|exists|some|with|in|iff|when|is|if)(?![\w\-])/, 'keyword.other'],

        // Module-qualified type name
        [/([a-z@][\w\-]*'*\/#?)+/, 'entity.name.variable'],

        // Type variable (lowercase single letter or _name)
        [/([_]?[a-z][0-9]*|_[\w\-]*'*|self)(?!\w)/, 'markup.italic'],

        // Type constructor / kind (Uppercase)
        [/[A-Z](?![\w\-])/, 'support.type'],

        // Named type identifier (lowercase, multi-char)
        [/[$]?[a-z@][\w\-]*'*/, 'support.type'],

        // Type-level punctuation
        [/[;,]|:(?!:)/, 'support.type'],

        // Nested angle brackets for type applications
        [/<(?![%&*+@!/\\\^~=.:\-?|\s\d])/, 'support.type', '@typeAngle'],
        [/\(/, 'support.type', '@typeParens'],
        [/\[/, 'support.type', '@typeBrackets'],

        // Exit type state on any of these
        [/(?=[,)\{}[\]=;"`A-Z]|[ \t]{2,}|\n)/, { token: '', next: '@pop' }],
        [
          /(?=\b(?:infix[rl]?|inline|noinline|fip|fbip|tail|value|reference|open|extend|rec|co|lazy|type|linear|effect|ambient|alias|extern|fn|fun|function|val|raw|final|ctl|var|con|if|then|else|elif|match|inject|mask|named|handle|handler|return|module|import|as|pub|abstract)(?![\w\-?']))/,
          { token: '', next: '@pop' },
        ],
      ],

      typeAngle: [
        [/>|\n|[ \t]{2}/, 'support.type', '@pop'],
        [/<(?![%&*+@!/\\\^~=.:\-?|])/, 'support.type', '@push'],
        { include: '@typeInner' },
      ],

      typeParens: [
        [/\)/, 'support.type', '@pop'],
        { include: '@typeInner' },
      ],

      typeBrackets: [
        [/\]/, 'support.type', '@pop'],
        { include: '@typeInner' },
      ],

      typeInner: [
        [/[ \t]+/, 'support.type'],
        [/(->|::?|\.)(?![$%&*+@!\\\^~=.:\-?|<>])/, 'support.type'],
        [/\b(forall|exists|some|with|in|iff|when|is|if)(?![\w\-])/, 'keyword.other'],
        [/([a-z@][\w\-]*'*\/#?)+/, 'entity.name.variable'],
        [/([_]?[a-z][0-9]*|_[\w\-]*'*|self)(?!\w)/, 'markup.italic'],
        [/[A-Z](?![\w\-])/, 'support.type'],
        [/[$]?[a-z@][\w\-]*'*/, 'support.type'],
        [/[;,:]/, 'support.type'],
        [/\/\*/, 'comment.block', '@blockComment'],
        [/\/\/.*$/, 'comment.line'],
      ],
    },
  } as Monaco.languages.IMonarchLanguage);

  // ── Completion provider (keyword snippets + more) ─────────────────────────
  registerCompletions(monaco);
}

// ── Completions ───────────────────────────────────────────────────────────────

function registerCompletions(monaco: typeof Monaco): void {
  monaco.languages.registerCompletionItemProvider(KOKA_LANGUAGE_ID, {
    provideCompletionItems(model, position) {
      const word = model.getWordUntilPosition(position);
      const range: Monaco.IRange = {
        startLineNumber: position.lineNumber,
        endLineNumber:   position.lineNumber,
        startColumn:     word.startColumn,
        endColumn:       word.endColumn,
      };

      const snippet = (
        label: string,
        insertText: string,
        documentation: string,
      ): Monaco.languages.CompletionItem => ({
        label,
        kind:  monaco.languages.CompletionItemKind.Snippet,
        insertText,
        insertTextRules: monaco.languages.CompletionItemInsertTextRule.InsertAsSnippet,
        documentation,
        range,
      });

      const kw = (label: string): Monaco.languages.CompletionItem => ({
        label,
        kind:  monaco.languages.CompletionItemKind.Keyword,
        insertText: label,
        range,
      });

      const suggestions: Monaco.languages.CompletionItem[] = [
        // ── Snippets ────────────────────────────────────────────────────
        snippet(
          'fun',
          'fun ${1:name}(${2:args})\n  ${3:body}',
          'Define a function',
        ),
        snippet(
          'fn',
          'fn(${1:args}) ${2:body}',
          'Anonymous function (lambda)',
        ),
        snippet(
          'match',
          'match ${1:expr}\n  ${2:pattern} -> ${3:result}',
          'Pattern match expression',
        ),
        snippet(
          'effect',
          'effect ${1:Name}\n  ctl ${2:op}(${3:args}) : ${4:result}',
          'Declare an algebraic effect',
        ),
        snippet(
          'handler',
          'handler\n  return(${1:x}) -> ${2:x}\n  ${3:op}(${4:args}) -> ${5:body}',
          'Define an effect handler',
        ),
        snippet(
          'with handler',
          'with handler\n  return(${1:x}) -> ${2:x}\n  ${3:op}(${4:args}) -> ${5:body}\n${6:body}',
          'With-handler expression',
        ),
        snippet(
          'type',
          'type ${1:Name}\n  ${2:Constructor}(${3:fields})',
          'Declare a type',
        ),
        snippet(
          'alias',
          'alias ${1:Name} = ${2:Type}',
          'Type alias',
        ),
        snippet(
          'struct',
          'struct ${1:name}\n  ${2:field} : ${3:Type}',
          'Struct declaration',
        ),
        snippet(
          'if-then-else',
          'if ${1:condition} then ${2:true-branch} else ${3:false-branch}',
          'If-then-else expression',
        ),
        snippet(
          'module',
          'module ${1:name}',
          'Module declaration',
        ),
        snippet(
          'import',
          'import ${1:module}',
          'Import a module',
        ),

        // ── Plain keywords ───────────────────────────────────────────────
        ...ALL_KEYWORDS.map(kw),
      ];

      return { suggestions };
    },
  });
}
