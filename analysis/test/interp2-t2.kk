
type surface
  SLit( i : int )
  SVar( name : string )
  // Generic primitive: op name and list of args
  SPrim( op : string, args : list<surface> ) 
  // Multi-parameter lambda
  SLam( params : list<string>, body : surface )
  // Multi-argument application
  SApp( fnx : surface, args : list<surface> )
  // Let binding: let x = e1 in e2
  SLet( name : string, expr : surface, body : surface )

// ---------------------------------------------------------
// 2. Core Syntax (The "IR")
// ---------------------------------------------------------

type term
  Lit( i : int )
  Var( name : string )
  Prim( op : string, args : list<term> )
  Lam( params : list<string>, body : term )
  App( fnx : term, args : list<term> )

type value
  VInt( i : int )
  VClos( params : list<string>, body : term, captured : list<(string,value)> )

// ---------------------------------------------------------
// 3. The Desugaring Pass
// ---------------------------------------------------------
// Converts Surface -> Core
// Logic: 'let x = v in b'  ==>  '(\x -> b)(v)'

fun desugar( s : surface ) : div term
  match s
    SLit(i) -> Lit(i)
    SVar(n) -> Var(n)
    SPrim(op, args) -> Prim(op, args.map(desugar))
    SLam(ps, b)     -> Lam(ps, desugar(b))
    SApp(f, args)   -> App(desugar(f), args.map(desugar))
    
    // The transformation:
    SLet(name, expr, body) -> 
      App( 
        Lam( [name], desugar(body) ), 
        [desugar(expr)] 
      )

// ---------------------------------------------------------
// 4. Effects
// ---------------------------------------------------------

effect env
  ctl lookup( name : string ) : value
  ctl snapshot() : list<(string,value)>

// ---------------------------------------------------------
// 5. Handlers
// ---------------------------------------------------------

fun run-env( current-env : list<(string,value)>, action : () -> <env,exn|e> a ) : <exn|e> a
  handle(action)
    ctl lookup(name)
      match current-env.find( fn(entry) entry.fst == name )
        Just( (_, v) ) -> resume(v)
        Nothing        -> throw("Runtime Error: Variable '" ++ name ++ "' not found")
    ctl snapshot()
      resume(current-env)

fun run-safe( action : () -> <exn|e> a, ?a/show: a -> e string) : e string
  with handler
    return(x)     x.show
    final ctl throw-exn(msg) "FAILURE: " ++ msg.show
  action()

fun show( v : value ) : string
  match v
    VInt(i) -> i.show
    VClos   -> "<closure>"

// ---------------------------------------------------------
// 6. Primitive Logic
// ---------------------------------------------------------

fun eval-prim( op : string, args : list<value> ) : <exn> value
  match (op, args)
    // Binary Add
    ("+", [VInt(a), VInt(b)]) -> VInt(a + b)
    // Binary Sub
    ("-", [VInt(a), VInt(b)]) -> VInt(a - b)
    // Binary Mult
    ("*", [VInt(a), VInt(b)]) -> VInt(a * b)
    // N-ary Sum (just for fun)
    ("sum", xs) -> 
       val total = xs.foldl(0, fn(acc, v) 
         match v 
           VInt(k) -> acc + k
           _       -> 0 // Ignore non-ints or throw
       )
       VInt(total)
    
    _ -> throw("Primitive error: Unknown op '" ++ op ++ "' or invalid args")

// ---------------------------------------------------------
// 7. The Evaluator
// ---------------------------------------------------------

fun eval( t : term ) : <env,exn,div> value
  match t
    Lit(i) -> VInt(i)
    Var(x) -> lookup(x)
    
    Prim(op, args) ->
      // Evaluate all arguments first (strict evaluation)
      val arg-vals = args.map(eval)
      eval-prim(op, arg-vals)

    Lam(ps, b) -> 
      val cap = snapshot()
      VClos(ps, b, cap)

    App(f, args) ->
      val func-val = eval(f)
      val arg-vals = args.map(eval)
      
      match func-val
        VClos(params, body, saved-env) ->
          if params.length != arg-vals.length then
             throw("Arity Mismatch: Expected " ++ params.length.show ++ " args, got " ++ arg-vals.length.show)
          
          // Zip parameters with values to create bindings
          val bindings = params.zip(arg-vals)
          
          // Extend the captured environment
          val new-env = bindings ++ saved-env
          
          run-env(new-env)
            eval(body)
            
        _ -> throw("Type Error: Application on non-function")

fun interpret( s : surface ) : <div,exn> string
  val core = desugar(s)
  // Run with empty env
  val res = run-env([]) 
    eval(core)
  "Result: " ++ res.show

fun analyze-t2()
  val t2 = SApp(
    SLam( ["x", "y"], SPrim("-", [SVar("x"), SVar("y")]) ),
    [ SLit(10), SLit(4) ]
  )
  run-safe(?a/show=id) { interpret(t2) }
fun result-t2()
  "Result: 6"
