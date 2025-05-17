import LeanVips.Asm.Basic
import Cli

namespace LeanVips.Instr

open Reg

def progToString (prog: Prog) : String :=
  prog.foldr (λ i l => (i.toString ++ "\n" ++ l)) ""


#eval zero.toString
#eval (and t0 t1 t2).toString

def p: Prog := #[
  andi t0 t1 100,
  sub  t1 t2 t0
]

#eval progToString p

def progToFile (path: String) (prog: Prog) := do
  return ← IO.FS.writeFile path (progToString prog)

#eval progToFile "asm.s" p


--def save (List Instr)

open Cli
