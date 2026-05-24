/-
  opus_Fhot.lean — Hot-path optimization of `Vm.step` focused on MOD.

  Optimization strategy:
    The profiler reported MOD as ~70% of `step`. The naive MOD body
    computes `regGet s.regs a % (Nat.max bv 1)`. `Nat.max` on
    arbitrary-precision Nat reduces via `Nat.decLe`, which is a
    branching unary-style decision; the divisor side `1` forces a
    full comparison even when `bv` is a small literal.

    We replace it with a direct `if bv = 0 then ... else ...` test
    (compiled as a single zero-check by the Lean runtime / native
    compiler), and mark a small `fastMod` helper `@[inline]` so the
    branch is fused into `step`. We also provide an `@[implemented_by]`
    fast version of `step` itself, so that `native_decide` (and any
    compiled caller) takes the MOD-fast path while the original
    definitional `step` remains bit-identical for kernel reduction.

    Equivalence: `Nat.max bv 1 = if bv = 0 then 1 else bv` for all
    `bv : Nat` (since `bv ≥ 1` iff `bv ≠ 0`). The `@[implemented_by]`
    runtime swap is therefore observationally identical — same output
    on every input, including the MOD-by-zero guard (`0 % 1 = 0`).
-/

namespace Vm

/-! ## Word and register semantics -/

def wordBits : Nat := 16
def wordMod  : Nat := 1 <<< wordBits   -- 2^16 = 65536

@[inline] def mask (n : Nat) : Nat := n % wordMod

def numRegs : Nat := 8

/-! ## Instruction set -/

inductive Instr where
  | NOP    : Instr
  | LOADI  : (dst : Nat) → (imm : Nat)        → Instr
  | MOV    : (dst src : Nat)                  → Instr
  | ADD    : (dst a b : Nat)                  → Instr
  | SUB    : (dst a b : Nat)                  → Instr
  | MUL    : (dst a b : Nat)                  → Instr
  | MOD    : (dst a b : Nat)                  → Instr
  | PUSH   : (src : Nat)                      → Instr
  | POP    : (dst : Nat)                      → Instr
  | JNZ    : (src : Nat) → (off : Int)        → Instr
  | HALT   : Instr
  deriving Repr, DecidableEq

abbrev Program := List Instr

structure State where
  regs    : List Nat
  stack   : List Nat
  pc      : Int
  halted  : Bool
  deriving Repr, DecidableEq

def initState : State :=
  { regs := List.replicate numRegs 0, stack := [], pc := 0, halted := false }

/-! ## Helpers -/

@[inline] def regGet (rs : List Nat) (i : Nat) : Nat :=
  rs.getD i 0

def regSet : List Nat → Nat → Nat → List Nat
  | [],       _,   _ => []
  | _ :: xs, 0,   v => v :: xs
  | x :: xs, n+1, v => x :: regSet xs n v

def fetch (prog : Program) (pc : Int) : Instr :=
  if pc < 0 then Instr.HALT
  else (prog[pc.toNat]?).getD Instr.HALT

/-! ## Fast MOD helper

  Bit-identical to `a % (Nat.max b 1)` for every `a b : Nat`.
  - If `b = 0`: `Nat.max 0 1 = 1`, so `a % 1 = 0`; our branch returns `a % 1 = 0`. ✓
  - If `b ≠ 0`: `b ≥ 1`, so `Nat.max b 1 = b`; our branch returns `a % b`. ✓

  Marked `@[inline]` so the zero-test is fused into the MOD arm of `step`.
-/
@[inline] def fastMod (a b : Nat) : Nat :=
  if b = 0 then 0 else a % b

theorem fastMod_eq (a b : Nat) : fastMod a b = a % (Nat.max b 1) := by
  unfold fastMod
  cases b with
  | zero => simp [Nat.mod_one]
  | succ k => simp [Nat.max_eq_left (Nat.succ_le_succ (Nat.zero_le _))]

/-! ## The step function

  MOD arm uses `fastMod` directly (cheap zero-test + native `%`),
  instead of `Nat.max bv 1` (which would force a Nat-comparison chain).
-/

def step (prog : Program) (s : State) : State :=
  if s.halted then s
  else
    match fetch prog s.pc with
    | .NOP =>
        { s with pc := s.pc + 1 }
    | .LOADI dst imm =>
        { s with regs := regSet s.regs dst (mask imm), pc := s.pc + 1 }
    | .MOV dst src =>
        { s with regs := regSet s.regs dst (regGet s.regs src), pc := s.pc + 1 }
    | .ADD dst a b =>
        let v := mask (regGet s.regs a + regGet s.regs b)
        { s with regs := regSet s.regs dst v, pc := s.pc + 1 }
    | .SUB dst a b =>
        let v := mask (regGet s.regs a - regGet s.regs b)
        { s with regs := regSet s.regs dst v, pc := s.pc + 1 }
    | .MUL dst a b =>
        let v := mask (regGet s.regs a * regGet s.regs b)
        { s with regs := regSet s.regs dst v, pc := s.pc + 1 }
    | .MOD dst a b =>
        let bv := regGet s.regs b
        let v  := regGet s.regs a % (Nat.max bv 1)
        { s with regs := regSet s.regs dst v, pc := s.pc + 1 }
    | .PUSH src =>
        { s with stack := regGet s.regs src :: s.stack, pc := s.pc + 1 }
    | .POP dst =>
        match s.stack with
        | []       => { s with pc := s.pc + 1 }
        | x :: xs  => { s with regs := regSet s.regs dst x, stack := xs, pc := s.pc + 1 }
    | .JNZ src off =>
        if regGet s.regs src ≠ 0 then
          { s with pc := s.pc + off }
        else
          { s with pc := s.pc + 1 }
    | .HALT =>
        { s with halted := true }

/-! ## Fast runtime replacement

  `stepFast` is the MOD-optimized variant. It is observationally equal
  to `step` (proven below via `step_eq_stepFast`), and registered with
  `@[csimp]` so that compiled / native code (including `native_decide`)
  uses `stepFast` automatically.
-/

def stepFast (prog : Program) (s : State) : State :=
  if s.halted then s
  else
    match fetch prog s.pc with
    | .NOP =>
        { s with pc := s.pc + 1 }
    | .LOADI dst imm =>
        { s with regs := regSet s.regs dst (mask imm), pc := s.pc + 1 }
    | .MOV dst src =>
        { s with regs := regSet s.regs dst (regGet s.regs src), pc := s.pc + 1 }
    | .ADD dst a b =>
        let v := mask (regGet s.regs a + regGet s.regs b)
        { s with regs := regSet s.regs dst v, pc := s.pc + 1 }
    | .SUB dst a b =>
        let v := mask (regGet s.regs a - regGet s.regs b)
        { s with regs := regSet s.regs dst v, pc := s.pc + 1 }
    | .MUL dst a b =>
        let v := mask (regGet s.regs a * regGet s.regs b)
        { s with regs := regSet s.regs dst v, pc := s.pc + 1 }
    | .MOD dst a b =>
        -- Hot path: avoid `Nat.max bv 1`; use a single zero-check.
        let bv := regGet s.regs b
        let v  := fastMod (regGet s.regs a) bv
        { s with regs := regSet s.regs dst v, pc := s.pc + 1 }
    | .PUSH src =>
        { s with stack := regGet s.regs src :: s.stack, pc := s.pc + 1 }
    | .POP dst =>
        match s.stack with
        | []       => { s with pc := s.pc + 1 }
        | x :: xs  => { s with regs := regSet s.regs dst x, stack := xs, pc := s.pc + 1 }
    | .JNZ src off =>
        if regGet s.regs src ≠ 0 then
          { s with pc := s.pc + off }
        else
          { s with pc := s.pc + 1 }
    | .HALT =>
        { s with halted := true }

theorem step_eq_stepFast : @step = @stepFast := by
  funext prog s
  unfold step stepFast
  by_cases h : s.halted
  · simp [h]
  · simp [h]
    cases fetch prog s.pc <;> simp [fastMod_eq]

@[csimp] theorem step_eq_stepFast' : @step = @stepFast := step_eq_stepFast

def runFor : Nat → Program → State → State
  | 0,        _,    s => s
  | fuel+1,   prog, s =>
      if s.halted then s
      else runFor fuel prog (step prog s)

end Vm

/-! ## Downstream kernel-checked programs (unchanged) -/

namespace Vm

open Instr

def P1 : Program :=
  [ LOADI 0 0
  , LOADI 1 1
  , LOADI 2 10
  , ADD 0 0 1
  , ADD 3 3 1
  , SUB 4 2 3
  , JNZ 4 (-3)
  , HALT ]

def P2 : Program :=
  [ LOADI 0 7
  , PUSH 0
  , LOADI 0 11
  , PUSH 0
  , LOADI 0 13
  , PUSH 0
  , POP 0
  , POP 1
  , POP 2
  , HALT ]

def P3 : Program :=
  [ LOADI 0 5
  , LOADI 1 3
  , MOD 2 0 1
  , HALT ]

theorem p1_final_r0 :
    (regGet (runFor 100 P1 initState).regs 0) = 10 := by native_decide

theorem p2_final :
    let s := runFor 50 P2 initState
    regGet s.regs 0 = 13 ∧ regGet s.regs 1 = 11 ∧ regGet s.regs 2 = 7 := by
  native_decide

theorem p3_final_r2 :
    (regGet (runFor 10 P3 initState).regs 2) = 2 := by native_decide

end Vm
