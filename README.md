# lean_vips

A small Lean experiment to model the execution semantics of the VIPS subset of the MIPS instruction set. I like to express my gratitude to the Lean community and in particular Henrik Böving who patiently have guided me through the process to the current state of the development. 

## Install

The installation assumes you have VsCode installed and executable by running `code` in your terminal.


```shell
clone https://github.com/perlindgren/lean_vips.git
cd lean_vips
code .
```

Follow [Setting up Lean](https://lean-lang.org/documentation/setup/), to install Lean support on your system.

## Quick Use 

Open the `LeanVips/Basic.lean`file in VsCode.

You should se a Lean dropdown menu (∀) to the upper right of the file window. Use the dropdown to start `InfoView`.

In the `Lean InfoView`should now see the current status (state) of Lean, reflecting the position in the `LeanVips/Basic.lean`file.

### Evaluation

Put your cursor at the end of line as shown below: 

```lean
#eval toBv32 (and  t0 t1 t2) [Cursor here] 
```

In the `Info View` you should se the machine code (in binary hex) representation of the `and t0 t1 t2` Vips instruction, like this:

```lean
Basic.lean:7:28
  0x012a4024#32
```
The `#32` indicate that the resulting value is a 32-bit bit vector (more on `BitVec` later). 

You can try neighboring lines, and see the translation to binary for other instructions and/or change the *mnemonic* or *operands* (the *rd*, *rs*, *rt* arguments) to obtain the corresponding machine code. Hint, you can use this later for your lab5 programming exercise.

Now, put your cursor at the end of line:
```lean
#eval eval imem 9 0x00 rf dm -- [your cursor here]
```

Lean will show the result of evaluating the `eval` definition (function) as a tuple of three values `(RegisterFile,  DMem, Bv32)`. The first `RegisterFile` is the resulting register file (an array of 32 words), second `DMem` is the data memory (dynamic array being empty in this case) and third and last `Bv32` is the value of the program counter register.

Looking at the arguments of `eval imem 9 0x00 rf dm`. 
- `imem`is the instruction memory definition (our program to execute)
  ```
  bne  t2 zero 4,    --00 -- if t2 != 0 branch to 14
  addi t0 t0 0x20,   --04 -- t0 <- 0x20
  addi t1 t0 (-1),   --08 -- t1 <- 0x1f
  slt  t2 t1 t0,     --0c -- t2 <- 0x1f < 0x20
  j    0,            --10 -- jump to address 0
  slt  t3 t0 t1,     --14 -- t3 <- 0x20 < 0x1f
  andi t4 t1 0xF00F, --18 -- t4 <- 0x0000_000f
  ori  t5 t1 0xF00F  --20 -- t5 <- 0x0000_f00f
                     --24 -- index out of bounds
  ```
- `9`is the number of simulation steps we want to run (in this case 9).
- `0x00`is the initial value for the `pc` register (the instruction memory starts at address 0x00).
- `rf`is the initial state of the register file, declared to be a vector of 32, 0 valued words.
  ```lean
  def rf:  Regfile := Vector.mkVector 32 0
  ```
- `dm`is the initial state of the data memory, declared as an empty array.
  ```lean
  def dm : DMem := #[]
  ```

The state after simulating 9 instructions is presented as the tuple:

```lean
({ toArray := #[0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32,
                0x00000000#32, 0x00000020#32, 0x0000001f#32, 0x00000001#32, 0x00000000#32, 0x0000000f#32, 0x0000f01f#32,
                0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32,
                0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32,
                0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32],
   size_toArray := _ },
 #[],
 0x00000020#32)
```

Now we can look closer at the resulting register file. `rf[t0]` (the 9th element) holds the value `0x20` (as a result of `addi t0 t0 0x20`), `rf[t1]` (the 9th element) holds the value `0x1f` (as a result of `addi t1 t0 (-1)`), etc.

The data memory is untouched, so still `#[]`, while the resulting `pc` has the value `0x20`, which corresponds to the address of the last instruction of the program.

We can also pick the result apart like this:

```lean
#eval -- [place cursor here]
  let (rf, _dm, pc) := eval imem 9 0x00 rf dm -- state after executing 9 instructions
  (pc, rf[t0.toNat], rf[t1.toNat], rf[t2.toNat], rf[t3.toNat], rf[t4.toNat], rf[t5.toNat])
```

Now, you can try increase the number of instructions to simulate to 10.

```lean
#eval (eval imem 10 0x00 rf dm) [your cursor here]
```

This will result in an error (`index out of bounds`), as trying to read the instruction at address 0x24, which is outside of the defined instruction memory `imem`.

Already now you can use `lean_vips`, as a way to write and simulate VIPS assembly programs, without knowing exactly how the modelling of the VIPS in Lean is implemented.

You will find additional examples in the `LeanVips/Basic.lean`.

The `imem_sum`shows an imperative version of arithmetic summation. 

Notice here, the complete definition of VIPS in Lean is less than 100 lines of code (the rest of the code is examples and proofs), Lean as a programming language allows for succint "lean" implementations.

## The VIPS model in Lean

### Machine code and Assembly

The VIPS model is a subset of the MIPS32 ISA, refer to [MIPS Greencard](https://booksite.elsevier.com/9780124077263/downloads/COD_5e_Greencard.pdf) for the complete MIPS32 instruction set.


At hart of the model we define the data structures capturing the VIPS instruction set in [LeanVips/Asm.Basic.lean](./LeanVips/Asm/Basic.lean):

```lean
-- BitVectors
abbrev Bv32:  Type := BitVec 32
abbrev Bv16:  Type := BitVec 16
abbrev Bv26:  Type := BitVec 26

-- Registers
abbrev Reg  : Type := BitVec 5

-- Other fields
abbrev Op   : Type := BitVec 6
abbrev Funct: Type := BitVec 6
abbrev Shamt: Type := BitVec 5

inductive R where
  | and : R
  | or  : R
  | add : R
  | sub : R
  | slt : R
deriving Repr

inductive I where
  | andi : I
  | ori  : I
  | addi : I
  | slti : I
  | lw   : I
  | sw   : I
  | beq  : I
  | bne  : I
deriving Repr, BEq

inductive Instr where
  | i (i_op: I) (rs rt: Reg) (imm: Bv16) : Instr
  | r (r_op: R) (rs rt rd: Reg) : Instr
  | j (imm26: Bv26) : Instr
deriving Repr, Inhabited
```

`Instr` here is the top level type, with three variants (constructors) `i`, `r`, and `j` to capture the three instruction classes.

`Reg` is the type of registers where the `BitVec 5` type represents 5-bit values:

```lean
abbrev Reg  : Type := BitVec 5
```

Similarly, `Op`, `Funct` and `Shamt` fields are represented by `BitVector` types of corresponding width.

The `Reg` definition along with constructors `zero, at', v0` etc., are given in the `LeanVips/Reg.Basic.lean`.

Altogether the definitions now let us construct VIPS assembly instructions and check them, e.g.:

```lean
#check Instr.i I.andi t0 t1 42 [place cursor here]
``` 
Will give you:
```lean
Instr.i I.andi t0 t1 42 : Instr
```

Here `t0` gives the `rs` field (one of the source operands), and `t1` the `rt` field (the destination for the `addi`). You can try constructing a few other instructions to get the hang of it.

While possible to create machine code instructions, the syntax is inconvenient, so let us define some short-hands for assembly language input:

```lean
...
@[match_pattern] def addi (rt rs: Reg) (imm16: Bv16): Instr := .i .addi rs rt imm16
... 
```

You can now use these shorthands to construct VIPS assembly instructions, lets check this one: 

```lean
#check andi t1 t0 42 [place cursor here]
```

You should now have:
```lean
andi t1 t0 42 : Instr
```

Notice, here `Instr.i I.andi t0 t1 42 : Instr` and `andi t1 t0 42 : Instr`, are just two different ways to construct the exact same instruction. The `andi` constructor follows the assembly syntax with the `rt` (destination) field first, while the `Instr.i` constructor adheres to the machine level encoding of the fields.

So can we show that they are the same? Let us try this!

```lean
theorem andi_equal: andi t1 t0 42 = Instr.i I.andi t0 t1 42 :=
  by
   simp [andi]
```

The theorem states the equality, and is solved (proven) by the `simp` tactic, using the definition of `andi`.

As a sanity check, you may try introducing some error, e.g.:

```lean
theorem andi_equal: andi t1 t0 42 = Instr.i I.andi t0 t1 43 :=
  by
   simp [andi]
```

Now, the `by` gets *squiggled*, indicating that the attempted proof no longer holds (effectively 42 != 43).

Similarly, we can try another error:

```lean
theorem andi_equal: andi t1 t0 42 = Instr.i I.andi t1 t0 42 :=
  by
   simp [andi]
```

Also here the proof attempt fails, in this case due to the order of register operands.

To gain further confidence, we can generalize over all possible rs, rt and immediate assignments.

```lean
theorem andi_equal_quant: ∀ (rs rt imm16), andi rt rs imm16 = Instr.i I.andi rs rt imm16 :=
  by
   simp [andi]
```

With the current encoding is however harder to further generalize (showing that this holds for all the shorthands defined). Instead we show it case by case for each supported instruction. (Room for future improvement, in case larger subset of instructions should be supported.)

### Semantics

The interpretation of the VIPS instruction set is given in [LeanVips/Semantics.Basic.lean](./LeanVips/Semantics/Basic.lean). 

We start by modelling instruction and data memory:

- `IMem` as an array of `Instr` (see previous section). `IMem.r` implements read (word aligned addresses).
- `DMem` as an array of `Bv32` (words). `DMem.r` and `IMem.w` implements read/write (word aligned) correspondingly.

The `instr_eval` definition implements the interpretation (or virtual machine) from current state (instruction, program counter, register file, and data memory) to the next state (register file, data memory and program counter).

The implementation matches the instruction class (`R`, `I` and `J`), and implements the corresponding state transition according to [MIPS Greencard](https://booksite.elsevier.com/9780124077263/downloads/COD_5e_Greencard.pdf).

The `eval` definition caters for the transitive behavior by computing next state (`inst_eval`) and recursively calling `eval`. Termination is ensured by the `fuel` parameter that monotonically decrease for each instruction evaluation. Execution will be aborted in case either of the instruction or data memory accesses are out of bounds.

Examples of use are found in [LeanVips/Basic.lean](./LeanVips/Basic.lean).

### SerDe

In order to interact with the environment serialization (`toBv32`), and deserialization (`fromBv32`) are implemented in [LeanVips/SerDe.Basic.lean](./LeanVips/SerDe/Basic.lean). 

Formally, the assembly representation and the binary machine code forms a bijective relation (one-to-one correspondence).

```lean
theorem tofrom (i: Instr) : fromBv32 (toBv32 i) = i 
```

Examples of use are found in [LeanVips/Basic.lean](./LeanVips/Basic.lean).

## CLI

As a demonstration of Lean being able to produce executables, a CLI for converting `vips` programs, between `.hex` and `.s` (assembly) representation is provided in  [LeanVips/IO/Basic.lean](./LeanVips/IO/Basic.lean).

To generate an executable:

```shell
lake build
```

When loading the Lean project, a two instruction program is serialized to `asm.s` and  `asm.hex`:

```shell
andi t0, t1, 0xff9c
sub  t1, t2, t0
```

```shell
0x3128ff9c
0x01484822
```

As part of loading the Lean project, the CLI tool is invoked, converting the freshly generated `asm.s` and `asm.hex` files, generating `asm2.s`, `asm3.s`, `asm4.s`, `asm2.hex`, and `asm3.hex`.

To get the CLI help, you can run:

```shell
.lake/build/bin/vips  --help
```

To convert from hex to assembly, run:

```shell
.lake/build/bin/vips asm.hex asm_new.s
```

And back to hex:

```shell
.lake/build/bin/vips asm_new.s asm_new.hex 
```

The tool can generate several output files (based on the same input file):

```shell
.lake/build/bin/vips asm_new.s asm_new2.hex asm_new2.s
```

Notice, while the serialization between `BitVec` and `Instr` representations have been formalized and their conversions proven 1-1, the textual parsing, ASCII emission, and file IO currently remains unproven.

## Future work

The `lean_vips` project is currently a vehicle for learning and experimenting with various features of the Lean language and ITP.

Future work might improve and extend its capabilities, e.g.:

- CI testing.
- The proofs could be simplified by higher degree of automation.
- Higher level deductive reasoning using upcoming Hoare Logic library.




















