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
def parseIntBitVec {n: Nat} : Parser (BitVec n) := do
   let it ← curr_it
   let i ← parseInt
   let bv : BitVec n := i
   dbg_trace "i={i}, bv={bv}"
   if (i != bv.toInt) then
     let s ← extract_last it
     panic s!"literal {s} too large to fit in {n} bits"
   return bv

@[inline]
def parseNatBitVec {n: Nat} : Parser (BitVec n) := do
   let it ← curr_it
   let i ← parseNat
   let bv : BitVec n := i
   dbg_trace "i={i}, bv={bv}"
   if (i != bv.toNat) then
     let s ← extract_last it
     panic s!"literal {s} too large to fit in {n} bits"
   return bv

@[inline]
def parseIntBv32 : Parser Bv16 := do
  return (← digits)

#eval parseInt.run "78"
#eval parseInt.run "-4"
#eval parseInt.run "0x12"
#eval parseInt.run "-0x12"
#eval parseNat.run "-0x12"
#eval if let some (b: Bv16) := (parseIntBitVec.run "0x1234").toOption then b else 0
#eval if let some (b: Bv16) := (parseIntBitVec.run "0x12345").toOption then b else 0
#eval if let some (b: Bv16) := (parseIntBitVec.run "0xffff").toOption then b else 0  -- err
#eval if let some (b: Bv16) := (parseNatBitVec.run "0xffff").toOption then b else 0  -- ok
#eval if let some (b: Bv16) := (parseIntBitVec.run "-0xffff").toOption then b else 0
#eval if let some (b: Bv16) := (parseNatBitVec.run "-0xffff").toOption then b else panic "here"
#eval if let some (b: Bv16) := (parseIntBitVec.run "-0x8000").toOption then b else 0 -- largest neg number
