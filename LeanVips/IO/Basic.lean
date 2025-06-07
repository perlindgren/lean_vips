import LeanVips.Asm.Basic
import LeanVips.SerDe.Basic
import LeanVips.Parse.Basic
import Std.Internal.Parsec
import Cli

open Reg
open LeanVips.Instr

def progToHexString (prog: Prog) : String :=
  let bin := prog.foldr (λ i l => toBv32 i :: l) []
  bin.foldr (λ (i: Bv32) l => ("0x" ++ i.toHex ++ "\n" ++ l)) ""

#eval toString p
#eval progToHexString p

def progToFile (path: String) (prog: Prog) := do
  return ← IO.FS.writeFile path (toString prog)

#eval progToFile "asm.s" p

def progToBinFile (path: String) (prog: Prog) := do
  return ← IO.FS.writeFile path (progToHexString prog)

open Std.Internal.Parsec
open Std.Internal.Parsec.String

#eval parseHex.run "0xab"

@[inline]
def parseHex! (s: String) : Nat :=
  match (parseHex.run s) with
  | Except.ok n => n
  | _ => panic "parsing failed, expected hex value"

@[inline]
def instrOfNat (s: String) : LeanVips.Instr :=
  fromBv32 (parseHex! s)

def readHexFile (path: String) : IO Prog := do
  dbg_trace "-- reading file {path}"
  let f ← IO.FS.readFile path
  let il := f.split (·.isWhitespace)
  let il := il.filter (λ s => s !="")

  dbg_trace il
  let prog := (il.map instrOfNat).toArray
  dbg_trace "-- prog read \n{prog}"
  return prog

#eval progToBinFile "asm.hex" p

#eval do
  let prog ← readHexFile "asm.hex"
  dbg_trace toString prog
  return

def readAsmFile (path: String) : IO Prog := do
  dbg_trace "-- reading file {path}"
  let str : String ← IO.FS.readFile path
  let result <- IO.ofExcept <| parseProg.run str
  return result

#eval do
  let prog ← readAsmFile "asm.s"
  dbg_trace toString prog
  return

open Cli

def process_in_file (input: String) (verbose : Bool) : IO (Option Prog) := do
  let in_file : System.FilePath := input
  match in_file.extension with
  | .some "s" =>
    if verbose then dbg_trace "-- reading assembly file {input}"
    let p ← readAsmFile input
    if verbose then dbg_trace "-- read {p}"
    return .some p
  | .some "hex" =>
    if verbose then dbg_trace "-- reading hex file {input}"
    let p ← readHexFile input
    if verbose then dbg_trace "-- read {p}"
    return .some p
  | _ =>
    IO.println "expected extension [.hex | .s]"
    return .none

def process_out_file (output: String) (prog: Prog) (_verbose : Bool) := do
  let out_file : System.FilePath := output
  match out_file.extension with
  | .some "s"   => progToFile output prog
  | .some "hex" => progToBinFile output prog
  | _           => IO.println "expected extension [.hex | .s]"

def runExampleCmd (p : Parsed) : IO UInt32 := do
  let verbose : Bool := p.hasFlag "verbose"

  let input : String := p.positionalArg! "input" |>.as! String
  if let some prog ← process_in_file input verbose then
    let outputs : Array String := p.variableArgsAs! String
    for output in outputs do
      process_out_file output prog verbose

  return 0

def vipsCmd : Cmd := `[Cli|
  vips VIA runExampleCmd; ["1.1.0"]
  "`vips` executable model of a subset of the MIPS32 ISA."

  FLAGS:
    verbose;                   "`--verbose` output."

  ARGS:
    input : String;            "<input.{hex|s}> input file path. .hex for hex input, .s for assembly"
    ...outputs : String;       "[output.{hex|s}] output file paths. .hex for hex output, .s for assembly"

  EXTENSIONS:
    author "per.lindgren@ltu.se"
]

def main (args : List String) : IO UInt32 :=
  vipsCmd.validate args

#eval main <| "--verbose asm.hex".splitOn " "
#eval main <| "--verbose asm.hex asm2.hex asm2.s".splitOn " "
#eval main <| "--verbose asm.s asm3.hex asm3.s".splitOn " "
#eval main <| "--verbose asm3.s asm4.s".splitOn " "
