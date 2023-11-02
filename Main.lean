import «Leaff»
import Cli

open Cli

def runDiffCmd (p : Parsed) : IO UInt32 := do
  let input1   : String       := p.positionalArg! "input1" |>.as! String
  let input2   : String       := p.positionalArg! "input2" |>.as! String
  let outputs : Array String := p.variableArgsAs! String
  IO.println <| "Input: " ++ input1
  IO.println <| "Input: " ++ input2
  IO.println <| "Outputs: " ++ toString outputs

  if p.hasFlag "verbose" then
    IO.println "Flag `--verbose` was set."
  if p.hasFlag "invert" then
    IO.println "Flag `--invert` was set."
  if p.hasFlag "optimize" then
    IO.println "Flag `--optimize` was set."

  return 0

def diffCmd : Cmd := `[Cli|
  diffCmd VIA runDiffCmd; ["0.0.1"]
  "This string denotes the description of `diffCmd`."

  FLAGS: -- TODO copy some from actual diff / gitdiff e.g short, ignore certain diffs etc
    verbose;                    "Declares a flag `--verbose`. This is the description of the flag."
    i, invert;                  "Declares a flag `--invert` with an associated short alias `-i`."
    p, priority : Nat;          "Declares a flag `--priority` with an associated short alias `-p` " ++
                                "that takes an argument of type `Nat`."
    module : ModuleName;        "Declares a flag `--module` that takes an argument of type `ModuleName` " ++
                                "which be can used to reference Lean modules like `Init.Data.Array` " ++
                                "or Lean files using a relative path like `Init/Data/Array.lean`."

  ARGS:
    input1 : String;      "Either a filename with `.lean` or `.olean` extension " ++
                         "or a git commit like prefix `aedc01b08fc48b972c09a9d69a34bba706062078/Cache/Requests.lean`."
    input2 : String;       ""
    ...outputs : String; "Declares a variable argument <output>... " ++
                         "that takes an arbitrary amount of arguments of type `String`."

  -- The EXTENSIONS section denotes features that
  -- were added as an external extension to the library.
  -- `./Cli/Extensions.lean` provides some commonly useful examples.
  EXTENSIONS:
    author "alexjbest";
    defaultValues! #[("priority", "0")]
]

def main (args : List String) : IO UInt32 :=
  diffCmd.validate args
