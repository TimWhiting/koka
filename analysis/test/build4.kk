import std/num/random
// ---------------------------------------------------------
// 1. The Build Effect
// ---------------------------------------------------------

effect build
  // Request a file/target. Returns the content/result.
  ctl need( key : string ) : string
  // Log a message (Linear effect)
  fun log( msg : string ) : ()

// ---------------------------------------------------------
// 2. The Build Handler (The Engine)
// ---------------------------------------------------------

// We use a type alias for the Rule function: 
// It takes a key and produces a result, potentially triggering more builds.
alias rule-book = (string) -> <build,exn,div> string

fun make( target : string, rules : rule-book ) : <exn,console,div> string
  
  // 1. State: The Memoization Cache
  // Maps "filename" -> "content"
  var cache : list<(string,string)> := []
  
  // 2. State: The Cycle Detector
  // A stack of keys currently being built
  var stack : list<string> := []

  // 3. The Re-entrant Solver
  // We define this as a recursive function so we can call it 
  // recursively when we encounter a 'need' for a new key.
  fun solve( action) 
    handle(action)
      // Handle Logging
      fun log(msg) 
        println(msg)

      // Handle Dependencies
      ctl need(key)
        // A. Cycle Check
        if stack.any( fn(k) k == key ) then
           throw("Circular dependency detected: " ++ stack.join(" -> ") ++ " -> " ++ key)

        // B. Cache Check
        match cache.find( fn(entry) entry.fst == key )
          Just( (_, v) ) -> 
            // Cache Hit: Return immediately (do not run rule)
            resume(v)
          
          Nothing ->
            // Cache Miss: Build it.
            // Push key to stack
            stack := Cons(key, stack)
            
            // Log the start
            println("[Building] " ++ key ++ "...")
            
            // RECURSION: We run the rule for this key inside the 'solve' handler
            // This ensures dependencies of this key are also handled.
            val result = solve( fn() { rules(key) } )
            
            // Pop stack
            match stack 
              Cons(_, rest) -> stack := rest
              Nil -> () // Should not happen
            
            // Save to cache
            cache := Cons( (key, result), cache )
            
            // Resume the original request with the result
            resume(result)

  // Start the build process
  solve( fn() { need(target) } )

// ---------------------------------------------------------
// 3. Error Handling Wrapper
// ---------------------------------------------------------

// Separate handler for Exceptions, as requested.
fun run-safe( action : () -> <exn,console|e> a) : <console|e> either<string,a>
  with handler
    return(x) Right(x)
    // Catch the exception and print it nicely
    final ctl throw-exn(msg) 
      println("\n!!! BUILD FAILED !!!")
      println("Error: " ++ msg.show)
      Left(msg.message)
  action()

fun my-makefile2( key : string ) : <build,exn> string
  match key
    // --- Existing Rules ---
    "main.exe" ->
      val o1 = need("utils.o")
      val o2 = need("main.o")
      "BINARY(" ++ o1 ++ "+" ++ o2 ++ ")"
    "main.o"   -> "OBJECT(" ++ need("main.c") ++ ")"
    "utils.o"  -> "OBJECT(" ++ need("utils.c") ++ ")"
    "main.c"   -> "int main() { ... }"
    "utils.c"  -> "int helper() { ... }"
    "utils.h"  -> "#define VAL 1"

    // --- TEST CASE 4: Dynamic Dependencies ---
    // The "app" asks for "config". 
    // "config" tells us whether to include "feature-A" or "feature-B".
    // The build graph changes based on the content of "config".
    "app.pkg" ->
      trace("Reading config to determine dependencies...")
      val cfg = need("config.txt")
      
      if cfg == "release" then
        val lib = need("optimized.lib")
        "PACKAGE(RELEASE, " ++ lib ++ ")"
      else
        val lib = need("debug.lib")
        "PACKAGE(DEBUG, " ++ lib ++ ")"

    "config.txt"    -> "release" // Try changing this to "debug"
    "optimized.lib" -> "LIB(Opt)"
    "debug.lib"     -> "LIB(Dbg)"

    // --- TEST CASE 5: Fibonacci Stress Test ---
    // fib-5 depends on fib-4 and fib-3. 
    // This creates a dense DAG (Directed Acyclic Graph).
    // If caching fails, this runs in exponential time.
    key | key.starts-with("fib-").bool ->
      // Parse "fib-N"
      val n-str = key.trim-left("fib-")
      match n-str.parse-int
        Nothing -> throw("Invalid fib target: " ++ key)
        Just(n) ->
          if n <= 1 then 
            "1"
          else
            trace("Calculating " ++ key ++ " (needs " ++ (n - 1).show ++ " & " ++ (n - 2).show ++ ")...")
            val v1 = need("fib-" ++ (n - 1).show).parse-int.default(0)
            val v2 = need("fib-" ++ (n - 2).show).parse-int.default(0)
            (v1 + v2).show

    _ -> throw("No rule for: " ++ key)
fun analyze-mymakefile-example4()
  run-safe
    val res = make("app.pkg", my-makefile2)
    println("\n[Result] " ++ res)
    res
fun result-mymakefile-example4()
  Right("PACKAGE(RELEASE, LIB(Opt))")