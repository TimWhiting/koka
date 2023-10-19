(function (Prism) {
  // TODO: Consider extending from fsharp or clike

  let types = {
    pattern: /(([a-zA-Z0-9_\-\/<>\(\) ,|]+,)*[a-zA-Z0-9_\-\/<>\(\) ,|]+)/,
    inside: {
      'simple': /[a-zA-Z0-9_\-\/]+/,
      'function': {
        pattern: /([a-zA-Z0-9_\-\/<>\(\) ,|]+)\s*->\s*([a-zA-Z0-9_\-\/<>\(\) ,|]+)/,
        inside: {
          'punctuation': /[\)><\(,]|(->)/,
          "types": {
            pattern: /[a-zA-Z0-9_\-\/<>\(\) ,|]+/,
            inside: null
          },
        },
      },
      'parameterized': {
        pattern: /[a-zA-Z0-9_\-\/]+<([^,]*,)*[^,]+>/,
        inside: {
          'punctuation': /[\)><\(,]/,
          "types": {
            pattern: /[a-zA-Z0-9_\-\/<>\(\) ,|]+/,
            inside: null
          },
        },
      },
      'effect': {
        pattern: /<([^,]*,)*(|)?[^,]+>/,
        inside: {
          'punctuation': /[\)><\(,|]/,
          "types": {
            pattern: /[a-zA-Z0-9_\-\/<>\(\) ,|]+/,
            inside: null
          },
        },
      },
      'tuple': {
        pattern: /\(([^,]*,)*[^,]+\)/,
        inside: {
          'punctuation': /[\)><\(,|]/,
          "types": {
            pattern: /[a-zA-Z0-9_\-\/<>\(\) ,|]+/,
            inside: null
          },
        }
      },
      'punctuation': /[\)><\(,|]/,
    }
  }
  types.inside.parameterized.inside.types.inside = types;
  types.inside.tuple.inside.types.inside = types;
  Prism.languages.koka = {
    'comment': [
      {
        pattern: /(^|[^\\])\/\*[\s\S]*?(?:\*\/|$)/,
        lookbehind: true,
        greedy: true
      },
      {
        pattern: /(^|[^\\:])\/\/.*/,
        lookbehind: true,
        greedy: true
      }
    ],
    'string': {
      pattern: /"[^"]*"/,
      greedy: true
    },
    'function': [
      {
        // function call with dot syntax
        pattern: /(?:\.)[a-z][a-zA-Z0-9_\-\/]*/,
        inside: {
          'punctuation': /\./
        },
        lookbehind: true,
      },
		],
    'class-name': [  // types and class names
      { // after alias x =...
        pattern: /(\b(?:alias)\s+[a-zA-Z0-9_\-\/<>\(\) ,|]+\s*=\s*)[a-zA-Z0-9_\-\/<>\(\) ,|]+/,
        lookbehind: true,
        inside: {
          'types': types,
          'punctuation': /=/
        }
      },
      {  // after keywords
        pattern: /(\b(?:type|struct|effect|alias)\s+)[^\s]+/,
        lookbehind: true,
        inside: {
          'types': types,
        }
      },
      { // after colon
        pattern: /(?::\s*)([a-zA-Z0-9_\-\/<>\(\) ,|]+,)+([a-zA-Z0-9_\-\/<>\(\) ,|]+)/,
        lookbehind: true,
        inside: {
          'types': types,
          'punctuation': /[:\)><\(,|]/,
        }
      },
      { // after colon
        pattern: /(?::\s*)[a-zA-Z0-9_\-\/<>\(\) ,|]+/,
        lookbehind: true,
        inside: {
          'types': types,
          'punctuation': /[:\)><\(,|]/,
        }
      },
      { // Capitalized Identifiers
        pattern: /\b[A-Z][\w\-]*\b/
      }
    ],
    
    'builtin': /\b(?:finally|initially|for|int|char|bool|string|throw|while|print|println)\b/,
    'keyword': /\b(?:(value(?=\s+(type|struct)))|named|scoped|module|import|pub|extern|inline|with|fip|fbip|tail|fn|fun|if|then|else|elif|return|match|handle|handler|val|var|type|struct|effect|alias)\b/,
    'function-call': [
      { // function call -- below keyword so fn gets priority in fn()
        pattern: /[a-z][a-zA-Z0-9_\-\/]*(?=\()/,
        alias: 'function'
      },
    ],
    'operator': /[\$\%\&\*\+\~\!\\\^\#\=\.\:\-\?\|\<\>]+/,
    'punctuation': /[{}[\];(),.:]/,
    'boolean': /\b(?:False|True)\b/,
    'number': /\b0x[\da-f]+\b|(?:\b\d+(?:\.\d*)?|\B\.\d+)(?:e[+-]?\d+)?/i,
    // /[<>]=?|[!=]=?=?|--?|\+\+?|&&?|\|\|?|[?*/~^%]/,
  };
  console.log(Prism.languages.koka)

  Prism.languages.kk = Prism.languages.koka;
  Prism.languages.kt = Prism.languages.koka;
  Prism.languages.kts = Prism.languages.koka;
}(Prism));