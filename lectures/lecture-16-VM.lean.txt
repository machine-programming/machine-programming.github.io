/-
  A VIRTUAL MACHINE, DEFINED INSIDE LEAN
  Lecture 16 — Formal Program Verification.  No mathlib; `lean VM.lean` suffices.

  Last lecture we wrote *mathematics* in Lean.  Here we write a *language* in
  Lean: its syntax as a datatype, its semantics as a function.  A program is
  then ordinary data — we can compute with it, pattern-match on it, and
  quantify over it — which is what lets us state "for every input" theorems.

  The language is deliberately tiny.  There are no expressions: every
  instruction reads registers and writes one register, so `acc * i` is an
  instruction, not a subterm.  Three-address code, as a real compiler back end
  would emit.
-/










/-! ## Values and storage -/

/-- A register name.  The machine has arbitrarily many; they are numbered. -/
abbrev Register := Nat

/-! ## Registers -/

def x    : Register := 0
def y    : Register := 1
def acc  : Register := 2
def i    : Register := 3
def flag : Register := 4
def zero : Register := 5
def one  : Register := 6
def tmp  : Register := 7

/-- Everything the machine computes with is an integer. -/
abbrev Value := Int

/-- The register file: what every register currently holds. -/
abbrev RegisterFile := Register → Value

def SAMPLE_REGISTER_FILE : RegisterFile
  | 0 => 10   -- accessing register x (0th reg) results in 10
  | 1 => 20   -- accessing register y (1st reg) results in 20
  | _ => 0

#eval SAMPLE_REGISTER_FILE x

/-- `write regs r v` is the register file after storing `v` into register `r`. -/
def write (regs : RegisterFile) (r : Register) (v : Value) : RegisterFile :=
  fun queried => if queried = r then v else regs queried

/-- After setting register `r` to have value `v`, accessing `r` will get you `v` -/
@[simp]
theorem write_same (regs : RegisterFile) (r : Register) (v : Value) :
  (write regs r v) r = v :=
by
  simp [write]





























/-! ## Syntax: instructions

    Convention throughout: **sources first, destination last**. -/

inductive Instr where
  /-- `destination := value` -/
  | loadConst       (value : Value) (destination : Register)

  /-- `destination := source` -/
  | copy            (source destination : Register)
  | add             (left right destination : Register)
  | sub             (left right destination : Register)
  | mul             (left right destination : Register)

  /-- `destination := -source` -/
  | neg             (source destination : Register)

  /-- `destination := 1` if `left < right`, else `0`.  Comparison produces a
      VALUE; it does not affect control flow. -/
  | compareLessThan (left right destination : Register)

  /-- Continue at `target` if `condition` is non-zero; otherwise fall through.
      0 is false and anything else is true, so the 1 or 0 written by
      `compareLessThan` is exactly what this expects. -/
  | branchIf        (condition : Register) (target : Nat)

  /-- Jump directly to the target program counter -/
  | jump            (target : Nat)

  /-- Stop, yielding the contents of `result`. -/
  | halt            (result : Register)

-- Uppercase aliases, so a listing reads like assembly.
@[reducible] def CONST              := Instr.loadConst
@[reducible] def COPY               := Instr.copy
@[reducible] def ADD                := Instr.add
@[reducible] def SUB                := Instr.sub
@[reducible] def MUL                := Instr.mul
@[reducible] def NEG                := Instr.neg
@[reducible] def COMPARE_LESS_THAN  := Instr.compareLessThan
@[reducible] def BRANCH_IF          := Instr.branchIf
@[reducible] def JUMP               := Instr.jump
@[reducible] def RETURN             := Instr.halt

/-! (our assembly)
    ADD X 1 X

    (pseudo code)
    x := x + 1     -/
def add_1_to_itself (x : Register) : Instr := ADD x one x

























/-! ## Syntax: programs -/

/-- A program is its listing, addressed by line number (the program counter).
    Reading past the end gives `none`, which the machine treats as getting stuck. -/
abbrev Program := Nat → Option Instr

def ofList : List Instr → Program
  | [],      _     => none
  | i :: _,  0     => some i
  | _ :: is, n + 1 => ofList is n

@[simp] theorem ofList_nil (pc : Nat) : ofList [] pc = none := rfl
@[simp] theorem ofList_zero (ins : Instr) (rest : List Instr) :
    ofList (ins :: rest) 0 = some ins := rfl
@[simp] theorem ofList_succ (ins : Instr) (rest : List Instr) (n : Nat) :
    ofList (ins :: rest) (n + 1) = ofList rest n := rfl

/-- Write a listing as `{{ instr ; instr ; ... }}`. -/
syntax "{{" sepBy(term, ";") "}}" : term
macro_rules | `({{ $is;* }}) => `(ofList [$is,*])

/-! ## Programs -/

/-- Absolute value. -/
def absProgram : Program := {{
    CONST 0 zero                  -- 0:  zero := 0
  ; COMPARE_LESS_THAN x zero flag -- 1:  flag := (x < 0)
  ; BRANCH_IF flag 4              -- 2:  if flag, jump to line 4
  ; RETURN x                      -- 3:  return x
  ; NEG x tmp                     -- 4:  tmp := -x
  ; RETURN tmp                    -- 5:  return tmp
}}

/-- The larger of two registers. -/
def maxProgram : Program := {{
    COMPARE_LESS_THAN x y flag    -- 0:  flag := (x < y)
  ; BRANCH_IF flag 3              -- 1:  if flag, jump to line 3
  ; RETURN x                      -- 2:  return x
  ; RETURN y                      -- 3:  return y
}}



























/-! ## Semantics: the machine -/

/-- A machine state: which line we are on, and what the registers hold. -/
structure Machine where
  line      : Nat
  registers : RegisterFile

inductive Outcome where
  | running (next : Machine)
  | halted  (result : Value)
  | stuck

@[simp] def stepOnce (prog : Program) (m : Machine) : Outcome :=
  let regs := m.registers
  match prog m.line with
  | none                             => .stuck
  | some (.loadConst v d)            => .running ⟨m.line + 1, write regs d v⟩
  | some (.copy s d)                 => .running ⟨m.line + 1, write regs d (regs s)⟩
  | some (.add a b d)                => .running ⟨m.line + 1, write regs d (regs a + regs b)⟩
  | some (.sub a b d)                => .running ⟨m.line + 1, write regs d (regs a - regs b)⟩
  | some (.mul a b d)                => .running ⟨m.line + 1, write regs d (regs a * regs b)⟩
  | some (.neg s d)                  => .running ⟨m.line + 1, write regs d (-(regs s))⟩
  | some (.compareLessThan a b d)    =>
      .running ⟨m.line + 1, write regs d (if regs a < regs b then 1 else 0)⟩
  | some (.branchIf c t)             => .running ⟨if regs c ≠ 0 then t else m.line + 1, regs⟩
  | some (.jump t)                   => .running ⟨t, regs⟩
  | some (.halt r)                   => .halted (regs r)

/-- Run for at most `fuel` steps.  `none` means it did not produce an answer —
    it ran out of fuel, or it got stuck.

    Fuel is what makes a possibly-non-terminating machine a TOTAL Lean function.
    It also turns termination into a statement we can prove or refute:
    "this program halts" is exactly "∃ fuel", so "this program loops forever"
    is "∀ fuel, the answer is `none`". -/
@[simp] def runFor (prog : Program) : Nat → Machine → Option Value
  | 0,          _ => none
  | fuel + 1,   m =>
    match stepOnce prog m with
    | .halted result => some result
    | .stuck         => none
    | .running m'    => runFor prog fuel m'

/-- `RUN prog FOR fuel FROM machine` -/
notation:max "RUN " p:max " FOR " n:max " FROM " m:max => runFor p n m
























/-! ## Termination, as a property of a program

    These two say nothing about what a program computes — only whether it ever
    answers.  They are stated once, over an arbitrary `prog`, and then proved
    about particular programs. -/

/-- `prog` answers from every starting register file. -/
def is_terminating (prog : Program) : Prop :=
  ∀ regs : RegisterFile, ∃ fuel result,
  RUN prog FOR fuel FROM ⟨0, regs⟩ = some result

/-- Some starting register file from which `prog` never answers, no matter how
    much fuel it is given.

    `none` covers two situations — the machine ran out of fuel, and the machine
    got stuck by running off the end of the listing.  Neither produces an
    answer, so both count as not terminating here. -/
def non_terminating (prog : Program) : Prop :=
  ∃ regs : RegisterFile, ∀ fuel,
  RUN prog FOR fuel FROM ⟨0, regs⟩ = none

/-- The two are exact opposites.  Worth stating, because it is what licenses
    proving non-termination directly instead of proving a negation. -/
theorem non_terminating_iff_not_terminating (prog : Program) :
    non_terminating prog ↔ ¬ is_terminating prog := by
  constructor
  · rintro ⟨regs, hnone⟩ hterm
    obtain ⟨fuel, result, hsome⟩ := hterm regs
    rw [hnone fuel] at hsome
    simp at hsome
  · intro hnot
    apply Classical.byContradiction
    intro hno
    apply hnot
    intro regs
    apply Classical.byContradiction
    intro hregs
    exact hno ⟨regs, fun fuel => by
      cases hrun : RUN prog FOR fuel FROM ⟨0, regs⟩ with
      | none   => rfl
      | some r => exact absurd ⟨fuel, r, hrun⟩ hregs⟩

/-- Reading a register you did not just write.  One lemma per ordered pair, so
    that register names never have to be unfolded inside a goal. -/
@[simp] theorem write_x_y (regs : RegisterFile) (v : Value) :
    write regs x v y = regs y := by simp [write, x, y]
@[simp] theorem write_x_acc (regs : RegisterFile) (v : Value) :
    write regs x v acc = regs acc := by simp [write, x, acc]
@[simp] theorem write_x_i (regs : RegisterFile) (v : Value) :
    write regs x v i = regs i := by simp [write, x, i]
@[simp] theorem write_x_flag (regs : RegisterFile) (v : Value) :
    write regs x v flag = regs flag := by simp [write, x, flag]
@[simp] theorem write_x_zero (regs : RegisterFile) (v : Value) :
    write regs x v zero = regs zero := by simp [write, x, zero]
@[simp] theorem write_x_one (regs : RegisterFile) (v : Value) :
    write regs x v one = regs one := by simp [write, x, one]
@[simp] theorem write_x_tmp (regs : RegisterFile) (v : Value) :
    write regs x v tmp = regs tmp := by simp [write, x, tmp]
@[simp] theorem write_y_x (regs : RegisterFile) (v : Value) :
    write regs y v x = regs x := by simp [write, y, x]
@[simp] theorem write_y_acc (regs : RegisterFile) (v : Value) :
    write regs y v acc = regs acc := by simp [write, y, acc]
@[simp] theorem write_y_i (regs : RegisterFile) (v : Value) :
    write regs y v i = regs i := by simp [write, y, i]
@[simp] theorem write_y_flag (regs : RegisterFile) (v : Value) :
    write regs y v flag = regs flag := by simp [write, y, flag]
@[simp] theorem write_y_zero (regs : RegisterFile) (v : Value) :
    write regs y v zero = regs zero := by simp [write, y, zero]
@[simp] theorem write_y_one (regs : RegisterFile) (v : Value) :
    write regs y v one = regs one := by simp [write, y, one]
@[simp] theorem write_y_tmp (regs : RegisterFile) (v : Value) :
    write regs y v tmp = regs tmp := by simp [write, y, tmp]
@[simp] theorem write_acc_x (regs : RegisterFile) (v : Value) :
    write regs acc v x = regs x := by simp [write, acc, x]
@[simp] theorem write_acc_y (regs : RegisterFile) (v : Value) :
    write regs acc v y = regs y := by simp [write, acc, y]
@[simp] theorem write_acc_i (regs : RegisterFile) (v : Value) :
    write regs acc v i = regs i := by simp [write, acc, i]
@[simp] theorem write_acc_flag (regs : RegisterFile) (v : Value) :
    write regs acc v flag = regs flag := by simp [write, acc, flag]
@[simp] theorem write_acc_zero (regs : RegisterFile) (v : Value) :
    write regs acc v zero = regs zero := by simp [write, acc, zero]
@[simp] theorem write_acc_one (regs : RegisterFile) (v : Value) :
    write regs acc v one = regs one := by simp [write, acc, one]
@[simp] theorem write_acc_tmp (regs : RegisterFile) (v : Value) :
    write regs acc v tmp = regs tmp := by simp [write, acc, tmp]
@[simp] theorem write_i_x (regs : RegisterFile) (v : Value) :
    write regs i v x = regs x := by simp [write, i, x]
@[simp] theorem write_i_y (regs : RegisterFile) (v : Value) :
    write regs i v y = regs y := by simp [write, i, y]
@[simp] theorem write_i_acc (regs : RegisterFile) (v : Value) :
    write regs i v acc = regs acc := by simp [write, i, acc]
@[simp] theorem write_i_flag (regs : RegisterFile) (v : Value) :
    write regs i v flag = regs flag := by simp [write, i, flag]
@[simp] theorem write_i_zero (regs : RegisterFile) (v : Value) :
    write regs i v zero = regs zero := by simp [write, i, zero]
@[simp] theorem write_i_one (regs : RegisterFile) (v : Value) :
    write regs i v one = regs one := by simp [write, i, one]
@[simp] theorem write_i_tmp (regs : RegisterFile) (v : Value) :
    write regs i v tmp = regs tmp := by simp [write, i, tmp]
@[simp] theorem write_flag_x (regs : RegisterFile) (v : Value) :
    write regs flag v x = regs x := by simp [write, flag, x]
@[simp] theorem write_flag_y (regs : RegisterFile) (v : Value) :
    write regs flag v y = regs y := by simp [write, flag, y]
@[simp] theorem write_flag_acc (regs : RegisterFile) (v : Value) :
    write regs flag v acc = regs acc := by simp [write, flag, acc]
@[simp] theorem write_flag_i (regs : RegisterFile) (v : Value) :
    write regs flag v i = regs i := by simp [write, flag, i]
@[simp] theorem write_flag_zero (regs : RegisterFile) (v : Value) :
    write regs flag v zero = regs zero := by simp [write, flag, zero]
@[simp] theorem write_flag_one (regs : RegisterFile) (v : Value) :
    write regs flag v one = regs one := by simp [write, flag, one]
@[simp] theorem write_flag_tmp (regs : RegisterFile) (v : Value) :
    write regs flag v tmp = regs tmp := by simp [write, flag, tmp]
@[simp] theorem write_zero_x (regs : RegisterFile) (v : Value) :
    write regs zero v x = regs x := by simp [write, zero, x]
@[simp] theorem write_zero_y (regs : RegisterFile) (v : Value) :
    write regs zero v y = regs y := by simp [write, zero, y]
@[simp] theorem write_zero_acc (regs : RegisterFile) (v : Value) :
    write regs zero v acc = regs acc := by simp [write, zero, acc]
@[simp] theorem write_zero_i (regs : RegisterFile) (v : Value) :
    write regs zero v i = regs i := by simp [write, zero, i]
@[simp] theorem write_zero_flag (regs : RegisterFile) (v : Value) :
    write regs zero v flag = regs flag := by simp [write, zero, flag]
@[simp] theorem write_zero_one (regs : RegisterFile) (v : Value) :
    write regs zero v one = regs one := by simp [write, zero, one]
@[simp] theorem write_zero_tmp (regs : RegisterFile) (v : Value) :
    write regs zero v tmp = regs tmp := by simp [write, zero, tmp]
@[simp] theorem write_one_x (regs : RegisterFile) (v : Value) :
    write regs one v x = regs x := by simp [write, one, x]
@[simp] theorem write_one_y (regs : RegisterFile) (v : Value) :
    write regs one v y = regs y := by simp [write, one, y]
@[simp] theorem write_one_acc (regs : RegisterFile) (v : Value) :
    write regs one v acc = regs acc := by simp [write, one, acc]
@[simp] theorem write_one_i (regs : RegisterFile) (v : Value) :
    write regs one v i = regs i := by simp [write, one, i]
@[simp] theorem write_one_flag (regs : RegisterFile) (v : Value) :
    write regs one v flag = regs flag := by simp [write, one, flag]
@[simp] theorem write_one_zero (regs : RegisterFile) (v : Value) :
    write regs one v zero = regs zero := by simp [write, one, zero]
@[simp] theorem write_one_tmp (regs : RegisterFile) (v : Value) :
    write regs one v tmp = regs tmp := by simp [write, one, tmp]
@[simp] theorem write_tmp_x (regs : RegisterFile) (v : Value) :
    write regs tmp v x = regs x := by simp [write, tmp, x]
@[simp] theorem write_tmp_y (regs : RegisterFile) (v : Value) :
    write regs tmp v y = regs y := by simp [write, tmp, y]
@[simp] theorem write_tmp_acc (regs : RegisterFile) (v : Value) :
    write regs tmp v acc = regs acc := by simp [write, tmp, acc]
@[simp] theorem write_tmp_i (regs : RegisterFile) (v : Value) :
    write regs tmp v i = regs i := by simp [write, tmp, i]
@[simp] theorem write_tmp_flag (regs : RegisterFile) (v : Value) :
    write regs tmp v flag = regs flag := by simp [write, tmp, flag]
@[simp] theorem write_tmp_zero (regs : RegisterFile) (v : Value) :
    write regs tmp v zero = regs zero := by simp [write, tmp, zero]
@[simp] theorem write_tmp_one (regs : RegisterFile) (v : Value) :
    write regs tmp v one = regs one := by simp [write, tmp, one]

/-- Start at line 0 with the given registers set and everything else zero. -/
def blank : RegisterFile := fun _ => 0
def startWith (assignments : List (Register × Value)) : Machine :=
  ⟨0, assignments.foldl (fun regs (r, v) => write regs r v) blank⟩

/-- Factorial.  Line 4 is the loop head; lines 7-9 are the body.

        acc := 1 ; i := x
        while 0 < i:
          acc := acc * i
          i := i - 1
        return acc
-/
def factorialProgram : Program := {{
    CONST 1 acc                   -- 0:  acc := 1
  ; COPY x i                      -- 1:  i := x
  ; CONST 0 zero                  -- 2:  zero := 0
  ; CONST 1 one                   -- 3:  one := 1
  ; COMPARE_LESS_THAN zero i flag -- 4:  flag := (0 < i)      <- loop head
  ; BRANCH_IF flag 7              -- 5:  if flag, enter the body
  ; RETURN acc                    -- 6:  otherwise return acc
  ; MUL acc i acc                 -- 7:    acc := acc * i
  ; SUB i one i                   -- 8:    i := i - 1
  ; JUMP 4                        -- 9:  end while
}}

/-- The same program with ONE instruction changed: line 8 adds instead of
    subtracting.  For any input `x ≥ 1` the counter only grows, the guard
    `0 < i` never fails, and the machine never reaches line 6. -/
def badFactorialProgram : Program := {{
    CONST 1 acc                   -- 0:  acc := 1
  ; COPY x i                      -- 1:  i := x
  ; CONST 0 zero                  -- 2:  zero := 0
  ; CONST 1 one                   -- 3:  one := 1
  ; COMPARE_LESS_THAN zero i flag -- 4:  flag := (0 < i)      <- loop head
  ; BRANCH_IF flag 7              -- 5:  if flag, enter the body
  ; RETURN acc                    -- 6:  otherwise return acc
  ; MUL acc i acc                 -- 7:    acc := acc * i
  ; ADD i one i                   -- 8:    i := i + 1          <-- THE BUG
  ; JUMP 4                        -- 9:  end while
}}

/-! ## The machine actually runs -/

#eval RUN absProgram        FOR 10 FROM (startWith [(x, -5)])
#eval RUN absProgram        FOR 10 FROM (startWith [(x,  7)])
#eval RUN maxProgram        FOR 10 FROM (startWith [(x, 3), (y, 9)])
#eval RUN factorialProgram  FOR 80 FROM (startWith [(x, 5)])
#eval RUN badFactorialProgram FOR 10000 FROM (startWith [(x, 1)])   -- never halts
