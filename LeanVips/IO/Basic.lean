import LeanVips.Asm.Basic
import LeanVips.SerDe.Basic
import Std.Internal.Parsec
import Cli

-- section file_handling

namespace LeanVips.Instr
open Reg

def progToString (prog: Prog) : String :=
  prog.foldr (λ i l => (i.toString ++ "\n" ++ l)) ""

def progToBinString (prog: Prog) : String :=
  let bin := prog.foldr (λ i l => (toBv32 i) :: l) []
  bin.foldr (λ (i: Bv32) l => (i.toHex ++ "\n" ++ l)) ""

#eval zero.toString
#eval (and t0 t1 t2).toString

def p: Prog := #[
  andi t0 t1 100,
  sub  t1 t2 t0
]

#eval progToString p
#eval progToBinString p

def progToFile (path: String) (prog: Prog) := do
  return ← IO.FS.writeFile path (progToString prog)

#eval progToFile "asm.s" p

def progToBinFile (path: String) (prog: Prog) := do
  return ← IO.FS.writeFile path (progToBinString prog)

open Std.Internal.Parsec
open Std.Internal.Parsec.String

@[inline]
def parseHex : Parser Nat := do
  return (← many1 hexDigit).reverse.foldr toHex 0
  where toHex c acc : Nat :=
    acc * 16 +
    if ('0' ≤ c ∧ c ≤ '9') then
      c.toNat - '0'.toNat
    else if ('a' ≤ c ∧ c ≤ 'f') then
      10 + c.toNat - 'a'.toNat
    else
      10 + c.toNat - 'A'.toNat

#eval parseHex.run "ab"

@[inline]
def parseHex! (s: String) : Nat :=
  match (parseHex.run s) with
  | Except.ok n => n
  | _ => panic "parsing failed, expected hex value"

@[inline]
def instrOfNat (s: String) : Instr :=
  fromBv32 (parseHex! s)

def fileBin (path: String) : IO Prog := do
  let f ←  IO.FS.readFile path
  let il := f.split (·.isWhitespace)
  let il := if il.getLast! = "" then il.take (il.length -1) else il

  dbg_trace il
  let prog := (il.map instrOfNat).toArray
  -- dbg_trace prog, missing ToString
  return prog

#eval progToBinFile "bin.txt" p

#eval do
  let prog ← fileBin "bin.txt"
  dbg_trace progToString prog
  return

end LeanVips.Instr

open Cli

def installCmd := `[Cli|
  installCmd NOOP;
  "installCmd provides an example for a subcommand without flags or arguments that does nothing. " ++
  "Versions can be omitted."
]

def testCmd := `[Cli|
  testCmd NOOP;
  "testCmd provides another example for a subcommand without flags or arguments that does nothing."
]

def runExampleCmd (p : Parsed) : IO UInt32 := do
  let input   : String       := p.positionalArg! "input" |>.as! String
  let outputs : Array String := p.variableArgsAs! String
  IO.println <| "Input: " ++ input
  IO.println <| "Outputs: " ++ toString outputs

  if p.hasFlag "verbose" then
    IO.println "Flag `--verbose` was set."
  if p.hasFlag "invert" then
    IO.println "Flag `--invert` was set."
  if p.hasFlag "optimize" then
    IO.println "Flag `--optimize` was set."

  let priority : Nat := p.flag! "priority" |>.as! Nat

  IO.println <| "Flag `--priority` always has at least a default value: " ++ toString priority

  if p.hasFlag "module" then
    let moduleName : ModuleName := p.flag! "module" |>.as! ModuleName
    IO.println <| s!"Flag `--module` was set to `{moduleName}`."


  if let some setPathsFlag := p.flag? "set-paths" then
    IO.println <| toString <| setPathsFlag.as! (Array String)
  return 0


def exampleCmd : Cmd := `[Cli|
  vips VIA runExampleCmd; ["0.0.1"]
  "`vips` executable model of a subset of the MIPS32 ISA."

  FLAGS:
    verbose;                    "Declares a flag `--verbose`. This is the description of the flag."
    i, invert;                  "Declares a flag `--invert` with an associated short alias `-i`."
    o, optimize;                "Declares a flag `--optimize` with an associated short alias `-o`."
    p, priority : Nat;          "Declares a flag `--priority` with an associated short alias `-p` " ++
                                "that takes an argument of type `Nat`."
    module : ModuleName;        "Declares a flag `--module` that takes an argument of type `ModuleName` " ++
                                "which be can used to reference Lean modules like `Init.Data.Array` " ++
                                "or Lean files using a relative path like `Init/Data/Array.lean`."
    "set-paths" : Array String; "Declares a flag `--set-paths` " ++
                                "that takes an argument of type `Array String`. " ++
                                "Quotation marks allow the use of hyphens."

  ARGS:
    input : String;      "Declares a positional argument <input> " ++
                         "that takes an argument of type `String`."
    ...outputs : String; "Declares a variable argument <output>... " ++
                         "that takes an arbitrary amount of arguments of type `String`."

  SUBCOMMANDS:
    installCmd;
    testCmd

  -- The EXTENSIONS section denotes features that
  -- were added as an external extension to the library.
  -- `./Cli/Extensions.lean` provides some commonly useful examples.
  EXTENSIONS:
    author "mhuisi";
    defaultValues! #[("priority", "0")]
]

def main (args : List String) : IO UInt32 :=
  exampleCmd.validate args

#eval main <| "-i -o -p 1 --module=Lean.Compiler --set-paths=path1,path2,path3 input output1 output2".splitOn " "
/-
Yields:
  Input: input
  Outputs: #[output1, output2]
  Flag `--invert` was set.
  Flag `--optimize` was set.
  Flag `--priority` always has at least a default value: 1
  Flag `--module` was set to `Lean.Compiler`.
  #[path1, path2, path3]
-/

-- Short parameterless flags can be grouped,
-- short flags with parameters do not need to be separated from
-- the corresponding value.
#eval main <| "-io -p1 input".splitOn " "
#eval main <| "-io -p1".splitOn " "
/-
Yields:
  Input: input
  Outputs: #[]
  Flag `--invert` was set.
  Flag `--optimize` was set.
  Flag `--priority` always has at least a default value: 1
-/

#eval main <| "--version".splitOn " "
/-
Yields:
  0.0.1
-/

#eval main <| "-h".splitOn " "
/-
Yields:
  0.0.1
-/
