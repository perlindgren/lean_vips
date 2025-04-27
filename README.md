# lean_vips

A small Lean experiment to model the execution semantics of the VIPS subset of the MIPS instruction set.

## Install

The installation assumes you have VsCode installed and executable by running `code` in your terminal.


```shell
clone https://github.com/perlindgren/lean_vips.git
cd lean_vips
code .
```

Follow [Setting up Lean](https://lean-lang.org/documentation/setup/), to install Lean support on your system.

## Quick Use (Assuming no prior Lean experience)

Open the `LeanVips/Basic.lean`file in VsCode.

You should se a Lean dropdown menu (∀) to the upper right of the file window. Use the dropdown to start `InfoView`.

In the `Lean InfoView`should now see the current status (state) of Lean, reflecting the position in the `LeanVips/Basic.lean`file.

### Evaluation

Put your cursor at the end of line 99. 

```lean
#eval (toBv32 (and  t0 t1 t2)) [Cursor here] 
```

In the `Info View` you should se the machine code (in binary hex) representation of the `and t0 t1 t2` Vips instruction, like this:

```lean
Basic.lean:99:0
  0x012a4024#32
```
The `#32` indicate that the resulting value is a 32-bit bit vector (more on `BitVec` later). 

You can try neighboring lines, and see the translation to binary for other instructions and/or change the `mnemonic` or operands (the rd, rs, rt arguments) to obtain the corresponding code. You can use this later for your lab5.

Put your cursor at the end of line 381.

```lean
#eval (eval imem 9 0x00 rf dm) [your cursor here]
```

Lean will show the result of evaluating the `eval` definition (function), as three values, the first is the resulting register file (an array of 32 words), second is the data memory (dynamic array being empty in this case) and lastly the value of the `pc` register.

Looking at the arguments of `eval imem 9 0x00 rf dm`. 
- `imem`is the instruction memory definition (our program to execute)
  ```
  bne  t1 zero 4,    --00 -- if t1 != 0 brach to 14
  addi t0 t0 0x20,   --04
  addi t1 t0 (-1),   --08
  slt  t2 t0 t1,     --0c
  j    0,            --10 -- jump to address 0
  slt  t3 t1 t0,     --14
  andi t4 t3 0xFFFF, --18
  ori  t5 t3 0xFFFF  --20
  ```
- `9`is the number of simulation steps we want to run (in this case 9).
- `0x00`is the initial value for the `pc` register (the instruction memory starts at address 0).
- `rf`is the initial state of the register file, declared at line 378 to be a vector of 32, 0 valued words.
- `dm`is the initial state of the data memory, declared at line 379 as empty

The state after simulating 9 instructions is:

```lean
({ toArray := #[0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32,
                0x00000000#32, 0x00000020#32, 0x0000001f#32, 0x00000000#32, 0x00000001#32, 0x00000001#32, 0x0000ffff#32,
                0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32,
                0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32,
                0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32],
   size_toArray := _ },
 #[],
 0x00000020#32)
```

Now we can look closer at the resulting register file. `rf[t0]` (the 8th element) holds the value `0x20` (as a result of `addi t0 t0 0x20`), `rf[t1]` (the 9th element) holds the value `0x1f` (as a result of `addi t1 t0 (-1)`), etc.

The data memory is untouched, so still `#[]`, while the resulting `pc` has the value `0x20`, which corresponds to the address of the last instruction of the program.

Now, you can try increase the number of instructions to simulate to 10.

```lean
#eval (eval imem 10 0x00 rf dm) [your cursor here]

```

This will result in an error (`index out of bounds`), as trying to read an instruction address outside of the defined instruction memory `imem`.

Already now you can use `lean_vips`, as a way to write and simulate VIPS assembly programs, without knowing exactly how the modelling in Lean is done.

Notice here, the complete definition of VIPS in Lean is less than 100 lines of code (the rest of the code is examples and proofs).

## The VIPS model in Lean

The 






