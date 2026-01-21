module analysis/loc-analysis

import std/core/list
import analysis/graph-data

// Main algorithm: Calculates transitive Line of Code cost
// Performs a depth-first traversal of the dependency DAG, summing LOC of unique nodes.
pub fun calculate-cost( root-name : string, g : graph ) : <div,console> int
  var visited : list<string> := []
  var total-loc := 0

  fun visit( current-name : string )
    // If already visited, skip to avoid double counting and infinite loops
    if visited.any( fn(n) n == current-name ) return ()
    
    // Mark as visited
    visited := Cons(current-name, visited)

    // Lookup node in the static graph
    match g.find( fn(n) n.name == current-name )
      Nothing -> 
        // If not found, we assume it's external or zero cost, or report warning
        // trace("Warning: Dependency '" ++ current-name ++ "' not found in graph.")
        () 
      Just(n) ->
        total-loc := total-loc + n.loc
        n.deps.foreach(visit)

  visit(root-name)
  total-loc

// Sort a list of (name, cost) pairs by cost
fun sort-by-cost( xs : list<(string, int)> ) : div list<(string, int)>
  match xs
    Nil -> Nil
    Cons(x, Nil) -> [x]
    _ -> 
      // Merge sort implementation
      val (left, right) = xs.split(xs.length / 2)
      merge(sort-by-cost(left), sort-by-cost(right))

fun merge( xs : list<(string, int)>, ys : list<(string, int)> ) : div list<(string, int)>
  match (xs, ys)
    (Nil, _) -> ys
    (_, Nil) -> xs
    (Cons((n1, c1), xx), Cons((n2, c2), yy)) ->
      if c1 <= c2 then
        Cons((n1, c1), merge(xx, ys))
      else
        Cons((n2, c2), merge(xs, yy))

// Generate a report for all analyze-* functions
pub fun generate-analyze-report( g : graph ) : <div,console> ()
  println("=== LOC Analysis Report for analyze-* Functions ===\n")
  
  // Filter all nodes that contain "analyze-" in their name
  val analyze-funcs = g.filter fn(n)
    n.name.contains("analyze-")
  
  // Calculate costs for each and create pairs
  val costs = analyze-funcs.map fn(n)
    (n.name, calculate-cost(n.name, g))
  
  // Sort by cost (ascending)
  val sorted = costs.sort-by-cost
  
  // Print sorted results
  var count := 0
  sorted.foreach fn((name, cost))
    count := count + 1
    println(name.pad-right(60) ++ " => " ++ cost.show.pad-left(6) ++ " LOC")
  
  println("\nTotal analyze functions: " ++ count.show)
  println("Note: LOC includes function itself plus all transitive dependencies")

// Example entry point to test the algorithm
pub fun main()
  println("--- LOC Analysis Algorithm Test ---")
  
  // Example Data
  val example-graph : graph = [
    Node("main", 10, ["helper1", "helper2"]),
    Node("helper1", 5, ["utils"]),
    Node("helper2", 5, ["utils"]),  // Both depend on utils ("diamond" dependency)
    Node("utils", 20, [])           // Should only be counted ONCE
  ]

  val cost = calculate-cost("main", example-graph)
  println("Calculated Cost for 'main': " ++ cost.show)
  println("Expected: 10 + 5 + 5 + 20 = 40 (utils counted once)")
  if cost == 40 then
    println("Test Passed\n")
  else
    println("Test Failed\n")
  
  // Now run the actual analysis on the real graph
  println("\n" ++ "=".repeat(80) ++ "\n")
  val actual-graph = graph-data/dependency-graph
  generate-analyze-report(actual-graph)
