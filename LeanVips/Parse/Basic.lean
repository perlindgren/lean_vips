import Std.Internal.Parsec
import LeanVips.Asm.Basic

open Std.Internal.Parsec
open Std.Internal.Parsec.String


@[inline]
def parseDec : Parser Nat := do
  return (← digits)

@[inline]
def parseHex : Parser Nat := do
  let _ ← pstring "0x"
  return ((← many1 hexDigit).reverse.foldr toHex 0)
  where toHex c acc : Nat :=
    acc * 16 +
    if ('0' ≤ c ∧ c ≤ '9') then
      c.toNat - '0'.toNat
    else if ('a' ≤ c ∧ c ≤ 'f') then
      10 + c.toNat - 'a'.toNat
    else
      10 + c.toNat - 'A'.toNat

@[inline]
def parseInt : Parser Int := do
  if (← peek!) == '-' then
    skip
    return - (← attempt parseHex <|> parseDec)
  else
    return ← attempt parseHex <|> parseDec

@[inline]
def parseNat : Parser Nat := do
  return ← attempt parseHex <|> parseDec

@[inline]
def curr_it : Parser String.Iterator := fun it =>
  .success it it

@[inline]
def extract_last (old_it : String.Iterator) : Parser String := fun it =>
  .success it (old_it.extract it)

@[inline]
def parseIntBitVec (n: Nat) : Parser (BitVec n) := do
   let it ← curr_it
   let i ← parseInt
   let bv : BitVec n := i
   dbg_trace "i={i}, bv={bv}"
   if (i != bv.toInt) then
     let s ← extract_last it
     panic s!"literal {s} too large to fit in signed {n} bits"
   return bv

@[inline]
def parseNatBitVec (n: Nat) : Parser (BitVec n) := do
   let it ← curr_it
   let i ← parseNat
   let bv : BitVec n := i
   dbg_trace "i={i}, bv={bv}"
   if (i != bv.toNat) then
     let s ← extract_last it
     panic s!"literal {s} too large to fit in unsigned {n} bits"
   return bv

#eval parseInt.run "78"
#eval parseInt.run "-4"
#eval parseInt.run "0x12"
#eval parseInt.run "-0x12"
#eval parseNat.run "-0x12"

#eval (parseIntBitVec 16).run "0x1234"  --ok
#eval (parseNatBitVec 16).run "0x1234"  --ok
#eval (parseIntBitVec 16).run "-0x1234" --ok
#eval (parseNatBitVec 16).run "-0x1234" --parse err
#eval (parseIntBitVec 16).run "0x12345" --error, too large
#eval (parseIntBitVec 16).run "0xffff"  --error, too large
#eval (parseNatBitVec 16).run "0xffff"  --ok
#eval (parseIntBitVec 16).run "-0xffff" --error, too large
#eval (parseNatBitVec 16).run "-0xffff" --parse err
#eval (parseIntBitVec 16).run "-0x8000" --ok, max neg

-- open LeanVips.Instr
open Reg

namespace LeanVips.Instr

set_option trace.profiler true in
@[inline]
def parseReg : Parser Reg := do
  let reg ←
    pstring "zero" <|>
    pstring "at"   <|>
    pstring "v0"   <|>
    pstring "v1"   <|>
    pstring "a0"   <|>
    pstring "a1"   <|>
    pstring "a2"   <|>
    pstring "a3"   <|>
    pstring "t0"   <|>
    pstring "t1"   <|>
    pstring "t2"   <|>
    pstring "t3"   <|>
    pstring "t4"   <|>
    pstring "t5"   <|>
    pstring "t6"   <|>
    pstring "t7"   <|>
    pstring "s0"   <|>
    pstring "s1"   <|>
    pstring "s2"   <|>
    pstring "s3"   <|>
    pstring "s4"   <|>
    pstring "s5"   <|>
    pstring "s6"   <|>
    pstring "s7"   <|>
    pstring "t8"   <|>
    pstring "t9"   <|>
    pstring "k0"   <|>
    pstring "k1"   <|>
    pstring "gp"   <|>
    pstring "sp"   <|>
    pstring "fp"   <|>
    pstring "ra"

  return match reg with
    | "zero" => zero
    | "at"   => at'
    | "v0"   => v0
    | "v1"   => v1
    | "a0"   => a0
    | "a1"   => a1
    | "a2"   => a2
    | "a3"   => a3
    | "t0"   => t0
    | "t1"   => t1
    | "t2"   => t2
    | "t3"   => t3
    | "t4"   => t4
    | "t5"   => t5
    | "t6"   => t6
    | "t7"   => t7
    | "s0"   => s0
    | "s1"   => s1
    | "s2"   => s2
    | "s3"   => s3
    | "s4"   => s4
    | "s5"   => s5
    | "s6"   => s6
    | "s7"   => s7
    | "t8"   => t8
    | "t9"   => t9
    | "k0"   => k0
    | "k1"   => k1
    | "gp"   => gp
    | "sp"   => sp
    | "fp"   => fp
    | "ra"   => ra
    | _ => unreachable!

def parseRType : Parser Instr := do
  let op_str ←
    pstring "and" <|>
    pstring "or"  <|>
    pstring "add" <|>
    pstring "sub" <|>
    pstring "slt"

  let _ ← ws
  let rd : Reg ← parseReg
  let _ ← ws
  let rs : Reg ← parseReg
  let _ ← ws
  let rt : Reg ← parseReg

  let op := match op_str with
    | "and" => R.and
    | "or"  => R.or
    | "add" => R.add
    | "sub" => R.sub
    | "slt" => R.slt
    | _     => unreachable!

  return Instr.r op rs rt rd

def parseIType : Parser Instr := do
  let op_str ←
    pstring "andi" <|>
    pstring "ori"  <|>
    pstring "addi" <|>
    pstring "slti" <|>
    pstring "lw"   <|>
    pstring "sw"   <|>
    pstring "beq"  <|>
    pstring "bne"

  let _ ← ws
  let rt : Reg ← parseReg
  let _ ← ws

  match op_str with
    | "lw"
    | "sw"   =>
      dbg_trace "-- Type I lw/sw"
      let imm16 ← parseIntBitVec 16
      let _ ← ws
      let rs ← parseReg
      let op := match op_str with
      | "lw"   => I.lw
      | "sw"   => I.sw
      | _      => unreachable!
      return Instr.i op rs rt imm16
    | _      =>
      dbg_trace "-- Type I"
      let (op, parse_imm) := match op_str with
        | "andi" => (I.andi, parseNatBitVec 16)
        | "ori"  => (I.ori,  parseNatBitVec 16)
        | "addi" => (I.addi, parseIntBitVec 16)
        | "slti" => (I.slti, parseIntBitVec 16)
        | "beq"  => (I.beq,  parseIntBitVec 16)
        | "bne"  => (I.bne,  parseIntBitVec 16)
        | _     => unreachable!

      let rs : Reg ← parseReg
      let _ ← ws
      let imm ← parse_imm
      return Instr.i op rs rt imm

def parseJType : Parser Instr := do
  let _ ← pstring "j"
  let _ ← ws
  let imm26 ← parseNatBitVec 26

  return Instr.j imm26

def parseInstr : Parser Instr := do
  let _ ← ws
  return ← attempt parseRType <|> parseIType <|> parseJType

#eval (parseInstr).run "and t0 t1 t2"
#eval (parseInstr).run "or zero at v0"
#eval (parseInstr).run "add zero at v0"

#eval (parseInstr).run "andi t0 t1 0x20"
#eval (parseInstr).run "ori s7 ra 0xffff"
#eval (parseInstr).run "beq k0 k0 0x7fff"
#eval (parseInstr).run "bne k0 k1 -0x8000"
#eval (parseInstr).run "lw k0 -0x8000 k1"
#eval (parseInstr).run "sw v1 -0x8000 v0"


#eval (parseInstr).run "j 9"
