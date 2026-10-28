import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BinaryPrograms
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.CounterForPrograms

namespace OAI.Algorithms

/-!
# Variable exponentiation with finite Boolean control

The exponent is a binary stack word.  The multiplication callback below uses
only fixed finite programs and leaves the countdown ports untouched.
-/

namespace SubexponentialSAT.PowerPrograms

open SubexponentialSAT.BitProgram
open SubexponentialSAT.StructuredProgram
open SubexponentialSAT.StructuredCalls
open SubexponentialSAT.BinaryArithmetic

abbrev Regs := Fin 8 → Bool
abbrev Data := StructuredProgram.State 8 9

/-- Base, exponent, accumulator, five work ports, and counter scratch. -/
def stackState (base exponent acc w₃ w₄ w₅ w₆ w₇ counterScratch : List Bool) :
    Fin 9 → List Bool := ![base, exponent, acc, w₃, w₄, w₅, w₆, w₇, counterScratch]

def state (r : Regs) (base exponent acc : List Bool) : Data :=
  ⟨r, stackState base exponent acc [] [] [] [] [] []⟩

@[simp] theorem stack_0 (b e a w₃ w₄ w₅ w₆ w₇ t : List Bool) :
    stackState b e a w₃ w₄ w₅ w₆ w₇ t 0 = b := rfl
@[simp] theorem stack_1 (b e a w₃ w₄ w₅ w₆ w₇ t : List Bool) :
    stackState b e a w₃ w₄ w₅ w₆ w₇ t 1 = e := rfl
@[simp] theorem stack_2 (b e a w₃ w₄ w₅ w₆ w₇ t : List Bool) :
    stackState b e a w₃ w₄ w₅ w₆ w₇ t 2 = a := rfl
@[simp] theorem stack_3 (b e a w₃ w₄ w₅ w₆ w₇ t : List Bool) :
    stackState b e a w₃ w₄ w₅ w₆ w₇ t 3 = w₃ := rfl
@[simp] theorem stack_4 (b e a w₃ w₄ w₅ w₆ w₇ t : List Bool) :
    stackState b e a w₃ w₄ w₅ w₆ w₇ t 4 = w₄ := rfl
@[simp] theorem stack_5 (b e a w₃ w₄ w₅ w₆ w₇ t : List Bool) :
    stackState b e a w₃ w₄ w₅ w₆ w₇ t 5 = w₅ := rfl
@[simp] theorem stack_6 (b e a w₃ w₄ w₅ w₆ w₇ t : List Bool) :
    stackState b e a w₃ w₄ w₅ w₆ w₇ t 6 = w₆ := rfl
@[simp] theorem stack_7 (b e a w₃ w₄ w₅ w₆ w₇ t : List Bool) :
    stackState b e a w₃ w₄ w₅ w₆ w₇ t 7 = w₇ := rfl
@[simp] theorem stack_8 (b e a w₃ w₄ w₅ w₆ w₇ t : List Bool) :
    stackState b e a w₃ w₄ w₅ w₆ w₇ t 8 = t := rfl

@[simp] theorem update_2 (b e a w₃ w₄ w₅ w₆ w₇ t next : List Bool) :
    Function.update (stackState b e a w₃ w₄ w₅ w₆ w₇ t) 2 next =
      stackState b e next w₃ w₄ w₅ w₆ w₇ t := by
  funext k; fin_cases k <;> simp [stackState]
@[simp] theorem update_3 (b e a w₃ w₄ w₅ w₆ w₇ t next : List Bool) :
    Function.update (stackState b e a w₃ w₄ w₅ w₆ w₇ t) 3 next =
      stackState b e a next w₄ w₅ w₆ w₇ t := by
  funext k; fin_cases k <;> simp [stackState]
@[simp] theorem update_4 (b e a w₃ w₄ w₅ w₆ w₇ t next : List Bool) :
    Function.update (stackState b e a w₃ w₄ w₅ w₆ w₇ t) 4 next =
      stackState b e a w₃ next w₅ w₆ w₇ t := by
  funext k; fin_cases k <;> simp [stackState]

def mulPorts (i : Fin 6) : Fin 9 := ![3, 2, 4, 5, 6, 7] i

theorem mulPorts_injective : Function.Injective mulPorts := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [mulPorts]

theorem extend_mulPorts (base exponent x y acc cp tmp rev : List Bool) :
    Function.extend mulPorts (SubexponentialSAT.BinaryPrograms.Mul.stackState x y acc cp tmp rev)
      (stackState base exponent [] [] [] [] [] [] []) =
      stackState base exponent y x acc cp tmp rev [] := by
  funext i
  fin_cases i
  · rw [Function.extend_apply']
    · rfl
    · rintro ⟨j, hj⟩; fin_cases j <;> simp [mulPorts] at hj
  · rw [Function.extend_apply']
    · rfl
    · rintro ⟨j, hj⟩; fin_cases j <;> simp [mulPorts] at hj
  · exact mulPorts_injective.extend_apply _ _ (1 : Fin 6)
  · exact mulPorts_injective.extend_apply _ _ (0 : Fin 6)
  · exact mulPorts_injective.extend_apply _ _ (2 : Fin 6)
  · exact mulPorts_injective.extend_apply _ _ (3 : Fin 6)
  · exact mulPorts_injective.extend_apply _ _ (4 : Fin 6)
  · exact mulPorts_injective.extend_apply _ _ (5 : Fin 6)
  · rw [Function.extend_apply']
    · rfl
    · rintro ⟨j, hj⟩; fin_cases j <;> simp [mulPorts] at hj

theorem embed_mul (r rf : Regs) (base exponent x y acc cp tmp rev : List Bool) :
    embedState id mulPorts (state r base exponent [])
      ⟨rf, SubexponentialSAT.BinaryPrograms.Mul.stackState x y acc cp tmp rev⟩ =
      ⟨rf, stackState base exponent y x acc cp tmp rev []⟩ := by
  simp [embedState, state, extend_mulPorts]

/-- The left operand is always a copy of the fixed base. -/
def nextAccumulator (base acc : List Bool) : List Bool :=
  SubexponentialSAT.BinaryPrograms.Mul.accumulate base acc []

@[simp] theorem nextAccumulator_value (base acc : List Bool) :
    BinaryArithmetic.toNat (nextAccumulator base acc) = BinaryArithmetic.toNat base * BinaryArithmetic.toNat acc := by
  simpa [nextAccumulator] using SubexponentialSAT.BinaryPrograms.Mul.accumulate_value base acc []

theorem nextAccumulator_length (base acc : List Bool) :
    (nextAccumulator base acc).length ≤ acc.length + base.length := by
  simpa [nextAccumulator] using SubexponentialSAT.BinaryPrograms.Mul.accumulate_length base acc []

/-- A specification of the successive accumulator words, not an instruction
that the compiled program evaluates on an unbounded natural register. -/
def iterateAccumulator (base : List Bool) : ℕ → List Bool → List Bool
  | 0, acc => acc
  | n + 1, acc => iterateAccumulator base n (nextAccumulator base acc)

theorem iterateAccumulator_value (base acc : List Bool) (n : ℕ) :
    BinaryArithmetic.toNat (iterateAccumulator base n acc) = BinaryArithmetic.toNat base ^ n * BinaryArithmetic.toNat acc := by
  induction n generalizing acc with
  | zero => simp [iterateAccumulator]
  | succ n ih => simp [iterateAccumulator, ih, pow_succ]; ring

theorem iterateAccumulator_length (base acc : List Bool) (n : ℕ) :
    (iterateAccumulator base n acc).length ≤ acc.length + n * base.length := by
  induction n generalizing acc with
  | zero => simp [iterateAccumulator]
  | succ n ih =>
      have ht := ih (nextAccumulator base acc)
      have hs := nextAccumulator_length base acc
      simp only [iterateAccumulator]
      simp only [Nat.add_mul, one_mul]
      omega

abbrev copyBase : StructuredCalls.Cmd 8 9 :=
  .call (SubexponentialSAT.StackRoutines.copyProgram 0 3 5 0 1)

abbrev multiply : StructuredCalls.Cmd 8 9 :=
  .call (SubexponentialSAT.ProgramLinking.liftProgram SubexponentialSAT.BinaryPrograms.Mul.program id mulPorts)

abbrev restore₁ : StructuredCalls.Cmd 8 9 :=
  .call (SubexponentialSAT.StackRoutines.transferProgram 4 3 0 1)

abbrev restore₂ : StructuredCalls.Cmd 8 9 :=
  .call (SubexponentialSAT.StackRoutines.transferProgram 3 2 0 1)

abbrev callback : StructuredCalls.Cmd 8 9 :=
  .seq copyBase (.seq multiply (.seq restore₁ restore₂))

theorem copy_eval (r : Regs) (base exponent acc : List Bool) :
    StructuredCalls.Eval copyBase (7 * base.length + 5) (state r base exponent acc)
      ⟨readRegs r 0 1 none, stackState base exponent acc base [] [] [] [] []⟩ := by
  apply StructuredCalls.Eval.call
  have h := SubexponentialSAT.StackRoutines.copyProgram_trace (0 : Fin 9) 3 5 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) r
    (stackState base exponent acc [] [] [] [] [] []) rfl
  have hh := SubexponentialSAT.StackRoutines.halt_after_trace _ h 7 rfl rfl
  convert hh using 1 <;>
    simp [state, State.withPC,
      SubexponentialSAT.StackRoutines.copyResult, SubexponentialSAT.StackRoutines.copyStacks]

theorem multiply_eval (r : Regs) (base exponent acc : List Bool) :
    ∃ rf : Regs, ∃ n ≤ 30 * (base.length + 1) * (acc.length + base.length + 1),
      StructuredCalls.Eval multiply n
        ⟨r, stackState base exponent acc base [] [] [] [] []⟩
        ⟨rf, stackState base exponent [] [] (nextAccumulator base acc) [] [] [] []⟩ := by
  obtain ⟨rf, n, hn, h⟩ := SubexponentialSAT.BinaryPrograms.Mul.run r base acc [] acc.length le_rfl (by simp)
  have ht := StructuredCalls.eval_call_lifted SubexponentialSAT.BinaryPrograms.Mul.program
    id mulPorts (state r base exponent []) Function.injective_id mulPorts_injective
    (a := ⟨r, SubexponentialSAT.BinaryPrograms.Mul.stackState base acc [] [] [] []⟩)
    (b := ⟨rf, SubexponentialSAT.BinaryPrograms.Mul.stackState [] [] (nextAccumulator base acc) [] [] []⟩) h
  refine ⟨rf, n, hn, ?_⟩
  simpa only [embed_mul] using ht

theorem restore₁_eval (r : Regs) (base exponent word : List Bool) :
    StructuredCalls.Eval restore₁ (3 * word.length + 3)
      ⟨r, stackState base exponent [] [] word [] [] [] []⟩
      ⟨readRegs r 0 1 none, stackState base exponent [] word.reverse [] [] [] [] []⟩ := by
  apply StructuredCalls.Eval.call
  have h := SubexponentialSAT.StackRoutines.transferProgram_trace (4 : Fin 9) 3 (0 : Fin 8) 1
    (by decide) (by decide) r (stackState base exponent [] [] word [] [] [] [])
  have hh := SubexponentialSAT.StackRoutines.halt_after_trace _ h 3 rfl rfl
  convert hh using 1 <;>
    simp [State.withPC,
      SubexponentialSAT.StackRoutines.transferResult, SubexponentialSAT.StackRoutines.transferStacks]

theorem restore₂_eval (r : Regs) (base exponent word : List Bool) :
    StructuredCalls.Eval restore₂ (3 * word.length + 3)
      ⟨r, stackState base exponent [] word.reverse [] [] [] [] []⟩
      (state (readRegs r 0 1 none) base exponent word) := by
  apply StructuredCalls.Eval.call
  have h := SubexponentialSAT.StackRoutines.transferProgram_trace (3 : Fin 9) 2 (0 : Fin 8) 1
    (by decide) (by decide) r (stackState base exponent [] word.reverse [] [] [] [] [])
  have hh := SubexponentialSAT.StackRoutines.halt_after_trace _ h 3 rfl rfl
  convert hh using 1 <;>
    simp [state, State.withPC,
      SubexponentialSAT.StackRoutines.transferResult, SubexponentialSAT.StackRoutines.transferStacks]

theorem callback_eval (r : Regs) (base exponent acc : List Bool) :
    ∃ rf : Regs, ∃ n ≤ 50 * (base.length + 1) * (acc.length + base.length + 1),
      StructuredCalls.Eval callback n (state r base exponent acc)
        (state rf base exponent (nextAccumulator base acc)) := by
  let r₁ := readRegs r 0 1 none
  obtain ⟨r₂, n, hn, hm⟩ := multiply_eval r₁ base exponent acc
  let r₃ := readRegs r₂ 0 1 none
  let r₄ := readRegs r₃ 0 1 none
  have ht := StructuredCalls.Eval.seq (copy_eval r base exponent acc)
    (StructuredCalls.Eval.seq hm
      (StructuredCalls.Eval.seq (restore₁_eval r₂ base exponent (nextAccumulator base acc))
        (restore₂_eval r₃ base exponent (nextAccumulator base acc))))
  refine ⟨r₄, _, ?_, ht⟩
  have hlen := nextAccumulator_length base acc
  let width := acc.length + base.length + 1
  have hscale : width ≤ (base.length + 1) * width := by
    simpa using Nat.mul_le_mul_right width (show 1 ≤ base.length + 1 by omega)
  calc
    _ ≤ n + 20 * width := by dsimp [width]; omega
    _ ≤ 30 * (base.length + 1) * width + 20 * ((base.length + 1) * width) :=
      Nat.add_le_add hn (Nat.mul_le_mul_left 20 hscale)
    _ = 50 * (base.length + 1) * (acc.length + base.length + 1) := by
      dsimp [width]
      ring

/-- The invariant ignores the countdown's two ports and all finite registers. -/
def Invariant (base : List Bool) (i : ℕ) (d : Data) : Prop :=
  d.stacks 0 = base ∧
  BinaryArithmetic.toNat (d.stacks 2) = BinaryArithmetic.toNat base ^ i ∧
  (d.stacks 2).length ≤ 1 + i * base.length ∧
  ∀ j : Fin 9, 3 ≤ j.val → j.val < 8 → d.stacks j = []

theorem invariant_initial (r : Regs) (base exponent : List Bool) :
    Invariant base 0 (state r base exponent [true]) := by
  refine ⟨rfl, by simp [state], by simp [state], ?_⟩
  intro j hj₁ hj₂
  fin_cases j <;> simp_all [state, stackState]

theorem invariant_stable (base : List Bool) (i : ℕ) {d e : Data}
    (hd : Invariant base i d)
    (hframe : ∀ j : Fin 9, j ≠ 1 → j ≠ 8 → e.stacks j = d.stacks j) :
    Invariant base i e := by
  rcases hd with ⟨hb, hv, hl, hw⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hframe 0 (by decide) (by decide)] using hb
  · simpa only [hframe 2 (by decide) (by decide)] using hv
  · simpa only [hframe 2 (by decide) (by decide)] using hl
  · intro j hj₁ hj₂
    rw [hframe j (by intro h; subst j; omega)
      (by intro h; subst j; omega)]
    exact hw j hj₁ hj₂

theorem state_of_invariant (base : List Bool) (i : ℕ) (d : Data)
    (hd : Invariant base i d) (hs : d.stacks 8 = []) :
    d = state d.regs base (d.stacks 1) (d.stacks 2) := by
  rcases hd with ⟨hb, hv, hl, hw⟩
  rcases d with ⟨r, stk⟩
  apply congrArg (State.mk r)
  funext j
  fin_cases j
  · exact hb
  · rfl
  · rfl
  · exact hw 3 (by decide) (by decide)
  · exact hw 4 (by decide) (by decide)
  · exact hw 5 (by decide) (by decide)
  · exact hw 6 (by decide) (by decide)
  · exact hw 7 (by decide) (by decide)
  · exact hs

def callbackBound (base : List Bool) (i : ℕ) : ℕ :=
  50 * (base.length + 1) * (2 + (i + 1) * base.length)

theorem callback_invariant (base : List Bool) (i : ℕ) (d : Data)
    (hd : Invariant base i d) (hs : d.stacks 8 = []) :
    ∃ n e, n ≤ callbackBound base i ∧ StructuredCalls.Eval callback n d e ∧
      e.stacks 1 = d.stacks 1 ∧ e.stacks 8 = [] ∧ Invariant base (i + 1) e := by
  obtain ⟨rf, n, hn, he⟩ := callback_eval d.regs base (d.stacks 1) (d.stacks 2)
  refine ⟨n, state rf base (d.stacks 1) (nextAccumulator base (d.stacks 2)), ?_, ?_, rfl, rfl, ?_⟩
  · have hlen := hd.2.2.1
    dsimp [callbackBound]
    apply hn.trans
    apply Nat.mul_le_mul_left
    simp only [Nat.add_mul, one_mul]
    omega
  · rwa [← state_of_invariant base i d hd hs] at he
  · refine ⟨rfl, ?_, ?_, ?_⟩
    · simp [state, hd.2.1, pow_succ, Nat.mul_comm]
    · have hlen := nextAccumulator_length base (d.stacks 2)
      have hold := hd.2.2.1
      change (nextAccumulator base (d.stacks 2)).length ≤ 1 + (i + 1) * base.length
      simp only [Nat.add_mul, one_mul]
      omega
    · intro j hj₁ hj₂
      fin_cases j <;> simp_all [state, stackState]

def ports : SubexponentialSAT.CounterForPrograms.Ports 8 9 where
  register := ⟨fun i => ⟨i.val, by omega⟩, by
    intro a b h
    apply Fin.ext
    exact congrArg (fun k : Fin 8 => k.val) h⟩
  counter := 1
  scratch := 8
  counter_ne_scratch := by decide

theorem invariant_frameStable (base : List Bool) :
    SubexponentialSAT.CounterForPrograms.FrameStable ports (Invariant base) := by
  intro i a b h hi
  apply invariant_stable base i hi
  intro j hj₁ hj₈
  exact (h j hj₁ hj₈).symm

theorem callback_spec (base : List Bool) :
    SubexponentialSAT.CounterForPrograms.BodySpec ports callback (Invariant base) (callbackBound base) := by
  intro i d hi hs _
  exact callback_invariant base i d hi hs

theorem callbackBound_monotone (base : List Bool) : Monotone (callbackBound base) := by
  intro i j hij
  dsimp [callbackBound]
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_right _
    (Nat.add_le_add_right hij 1)) 2)

abbrev initializeAccumulator : StructuredCalls.Cmd 8 9 :=
  .base (.seq (.atom (.set 0 true)) (.atom (.push 2 0)))

theorem initialize_eval (r : Regs) (base exponent : List Bool) :
    StructuredCalls.Eval initializeAccumulator 2 (state r base exponent [])
      (state (Function.update r 0 true) base exponent [true]) := by
  apply StructuredCalls.Eval.base
  have hs := StructuredProgram.Eval.atom (.set (0 : Fin 8) true) (state r base exponent [])
  have hp := StructuredProgram.Eval.atom (.push (2 : Fin 9) 0)
    (Atom.eval (.set (0 : Fin 8) true) (state r base exponent []))
  simpa [Atom.eval, Atom.instr, State.ofCfg, State.withPC, execInstr, state] using
    StructuredProgram.Eval.seq hs hp

/-- The only loop bound is the binary word on the exponent stack. -/
abbrev command : StructuredCalls.Cmd 8 9 :=
  .seq initializeAccumulator (SubexponentialSAT.CounterForPrograms.forCmd ports callback)

/-- A fixed 85-label program, independent of base and exponent. -/
def program := StructuredCalls.compiled command (0 : Fin 9) 2

theorem command_size : StructuredCalls.size command = 84 := by
  simp [
    StructuredCalls.size, StructuredProgram.size]

/-- A polynomial in numerical exponent and the actual input word lengths. -/
def workBound (base exponent : List Bool) : ℕ :=
  BinaryArithmetic.toNat exponent * callbackBound base (BinaryArithmetic.toNat exponent) +
    (BinaryArithmetic.toNat exponent + 1) * (16 * exponent.length + 16)

def runtimeBound (base exponent : List Bool) : ℕ := workBound base exponent + 3

theorem command_eval (r : Regs) (base exponent : List Bool) :
    ∃ n d, StructuredCalls.Eval command n (state r base exponent []) d ∧
      Invariant base (BinaryArithmetic.toNat exponent) d ∧ BinaryArithmetic.toNat (d.stacks 1) = 0 ∧
      (d.stacks 1).length = exponent.length ∧ d.stacks 8 = [] ∧
      n ≤ workBound base exponent + 2 := by
  obtain ⟨n, d, he, hi, hz, hw, hs, hn⟩ :=
    SubexponentialSAT.CounterForPrograms.for_correct ports callback (Invariant base) (callbackBound base)
      (invariant_frameStable base) (callback_spec base)
      (state (Function.update r 0 true) base exponent [true]) rfl
      (invariant_initial _ base exponent)
  have hb := SubexponentialSAT.CounterForPrograms.budgetSum_le_mono (callbackBound base)
    (callbackBound_monotone base) (BinaryArithmetic.toNat exponent)
  have hi' : Invariant base (BinaryArithmetic.toNat exponent) d := by
    simpa [state, ports, SubexponentialSAT.CounterPrograms.value_eq_toNat] using hi
  have hz' : BinaryArithmetic.toNat (d.stacks 1) = 0 := by
    simpa [ports, SubexponentialSAT.CounterPrograms.value_eq_toNat] using hz
  have hw' : (d.stacks 1).length = exponent.length := by
    simpa [state, ports] using hw
  have hn' : n ≤ SubexponentialSAT.CounterForPrograms.budgetSum (callbackBound base) 0 (BinaryArithmetic.toNat exponent) +
      (BinaryArithmetic.toNat exponent + 1) * (16 * exponent.length + 16) := by
    simpa [state, ports, SubexponentialSAT.CounterPrograms.value_eq_toNat] using hn
  refine ⟨2 + n, d, StructuredCalls.Eval.seq (initialize_eval r base exponent) he,
    hi', hz', hw', hs, ?_⟩
  dsimp [workBound]
  omega

/-- Complete natural-power correctness, including a bound for the actual raw
output representation and a halted instruction trace. Leading zeros are allowed. -/
theorem run_value (r : Regs) (base exponent : List Bool) :
    ∃ d : Data,
      BinaryArithmetic.toNat (d.stacks 2) = BinaryArithmetic.toNat base ^ BinaryArithmetic.toNat exponent ∧
      (d.stacks 2).length ≤ 1 + BinaryArithmetic.toNat exponent * base.length ∧
      d.stacks 0 = base ∧ BinaryArithmetic.toNat (d.stacks 1) = 0 ∧
      (d.stacks 1).length = exponent.length ∧
      (∀ j : Fin 9, 3 ≤ j.val → d.stacks j = []) ∧
      BitProgram.RunsIn program (runtimeBound base exponent)
        ((state r base exponent []).withPC (some program.entry)) (d.withPC none) := by
  obtain ⟨n, d, he, hi, hz, hw, hs, hn⟩ := command_eval r base exponent
  refine ⟨d, hi.2.1, hi.2.2.1, hi.1, hz, hw, ?_, n + 1, ?_,
    StructuredCalls.compiled_halt_trace he 0 2⟩
  · intro j hj
    by_cases hlast : j.val < 8
    · exact hi.2.2.2 j hj hlast
    · have heq : j = 8 := by apply Fin.ext; omega
      simpa [heq] using hs
  · dsimp [runtimeBound]
    omega

/-- The same fixed program runs on primitive tapes with a fixed compilation
factor multiplying the explicit polynomial arithmetic-work bound. -/
theorem primitive_value (r : Regs) (base exponent : List Bool) :
    ∃ d : Data,
      BinaryArithmetic.toNat (d.stacks 2) = BinaryArithmetic.toNat base ^ BinaryArithmetic.toNat exponent ∧
      (d.stacks 2).length ≤ 1 + BinaryArithmetic.toNat exponent * base.length ∧
      Computation.RunsIn (BitProgram.primitive program).step
        (BitProgram.primitiveOverhead program * runtimeBound base exponent)
        (BitProgram.primitiveCfg program ((state r base exponent []).withPC (some program.entry)))
        (BitProgram.primitiveCfg program (d.withPC none)) := by
  obtain ⟨d, hv, hl, _, _, _, _, hr⟩ := run_value r base exponent
  exact ⟨d, hv, hl, BitProgram.primitive_execution program hr⟩

end SubexponentialSAT.PowerPrograms

end OAI.Algorithms
