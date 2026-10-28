import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.CounterForPrograms

namespace OAI.Algorithms

/-!
# Saturating predecessor by fixed Boolean-stack code

A preserving zero scan guards the verified borrow routine.  Zero words, including
arbitrarily padded zero representations, are retained; positive words are
decremented without increasing their length. The callback-free code is total.
-/

namespace SubexponentialSAT.CounterPredProgram

open BitProgram StructuredProgram CounterPrograms CounterForPrograms

variable {R S : ℕ}

abbrev predCmd (p : Ports R S) : StructuredCalls.Cmd R S :=
  .seq (zeroCmd p) (.ite (p.register 2) (.base .skip) (decrementCmd p))

noncomputable def predResult (p : Ports R S) (d : Data R S) : Data R S :=
  if isZero (d.stacks p.counter) then zeroResult p d
  else decrementResult p (zeroResult p d)

def predCost (p : Ports R S) (d : Data R S) : ℕ :=
  (8 * (d.stacks p.counter).length + 6) +
    if isZero (d.stacks p.counter) then 1 else rippleCost false (d.stacks p.counter) + 2

@[simp] theorem zeroResult_counter (p : Ports R S) (d : Data R S) :
    (zeroResult p d).stacks p.counter = d.stacks p.counter := by simp [zeroResult]

@[simp] theorem zeroResult_scratch (p : Ports R S) (d : Data R S) :
    (zeroResult p d).stacks p.scratch = [] := by simp [zeroResult]

@[simp] theorem zeroResult_flag (p : Ports R S) (d : Data R S) :
    (zeroResult p d).regs (p.register 2) = isZero (d.stacks p.counter) := by
  simp [zeroResult]

theorem pred_eval (p : Ports R S) (d : Data R S) (hs : d.stacks p.scratch = []) :
    StructuredCalls.Eval (predCmd p) (predCost p d) d (predResult p d) := by
  cases hz : isZero (d.stacks p.counter) with
  | true =>
      have hf : (zeroResult p d).regs (p.register 2) = true := by simp [hz]
      have hi : StructuredCalls.Eval
          (.ite (p.register 2) (.base .skip) (decrementCmd p)) 1
          (zeroResult p d) (zeroResult p d) :=
        .ite_true hf (.base (.skip _))
      simpa [predCmd, predCost, predResult, hz] using (zero_eval p d hs).seq hi
  | false =>
      have hf : (zeroResult p d).regs (p.register 2) = false := by simp [hz]
      have hd := decrement_eval p (zeroResult p d) (zeroResult_scratch p d)
      have hi : StructuredCalls.Eval
          (.ite (p.register 2) (.base .skip) (decrementCmd p))
          (rippleCost false (d.stacks p.counter) + 2)
          (zeroResult p d) (decrementResult p (zeroResult p d)) := by
        simpa [Nat.add_assoc] using StructuredCalls.Eval.ite_false hf hd
      simpa [predCmd, predCost, predResult, hz] using (zero_eval p d hs).seq hi

@[simp] theorem predResult_counter (p : Ports R S) (d : Data R S) :
    (predResult p d).stacks p.counter =
      if isZero (d.stacks p.counter) then d.stacks p.counter
      else ripple false (d.stacks p.counter) := by
  cases h : isZero (d.stacks p.counter) <;> simp [predResult, h]

@[simp] theorem predResult_scratch (p : Ports R S) (d : Data R S) :
    (predResult p d).stacks p.scratch = [] := by
  cases h : isZero (d.stacks p.counter) <;> simp [predResult, h]

theorem predResult_value (p : Ports R S) (d : Data R S) :
    value ((predResult p d).stacks p.counter) = value (d.stacks p.counter) - 1 := by
  rw [predResult_counter]
  cases hz : isZero (d.stacks p.counter) with
  | true =>
      have hv := (isZero_eq_true_iff _).1 hz
      simp [hv]
  | false =>
      have hv := value_decrement ((isZero_eq_false_iff _).1 hz)
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega

theorem predResult_toNat (p : Ports R S) (d : Data R S) :
    BinaryArithmetic.toNat ((predResult p d).stacks p.counter) =
      BinaryArithmetic.toNat (d.stacks p.counter) - 1 := by
  simpa only [value_eq_toNat] using predResult_value p d

/-- Both branches preserve the raw representation width, even at zero. -/
theorem predResult_length (p : Ports R S) (d : Data R S) :
    ((predResult p d).stacks p.counter).length = (d.stacks p.counter).length := by
  rw [predResult_counter]
  cases hz : isZero (d.stacks p.counter) with
  | true => simp
  | false => simpa using decrement_length ((isZero_eq_false_iff _).1 hz)

theorem predResult_frame (p : Ports R S) (d : Data R S)
    (j : Fin S) (hc : j ≠ p.counter) (hs : j ≠ p.scratch) :
    (predResult p d).stacks j = d.stacks j := by
  cases hz : isZero (d.stacks p.counter) with
  | true =>
      simpa [predResult, hz, zeroResult] using
        install_other_stack p d false false (isZero (d.stacks p.counter))
          (d.stacks p.counter) [] j hc hs
  | false =>
      simp only [predResult, hz, Bool.false_eq_true, ↓reduceIte, decrementResult]
      rw [install_other_stack p (zeroResult p d) _ _ _ _ _ j hc hs]
      exact install_other_stack p d _ _ _ _ _ j hc hs

/-- The bound includes the compiled program's final halt instruction. -/
theorem predCost_le (p : Ports R S) (d : Data R S) :
    predCost p d + 1 ≤ 20 * ((d.stacks p.counter).length + 1) := by
  have hr := rippleCost_le false (d.stacks p.counter)
  cases h : isZero (d.stacks p.counter) <;> simp [predCost, h] <;> omega

/-- With empty incoming scratch, the counter is the only changed stack. -/
theorem predResult_stacks (p : Ports R S) (d : Data R S) (hs : d.stacks p.scratch = []) :
    (predResult p d).stacks =
      Function.update d.stacks p.counter ((predResult p d).stacks p.counter) := by
  funext j
  by_cases hc : j = p.counter
  · subst j
    simp
  · by_cases hscratch : j = p.scratch
    · subst j
      simp [Function.update_of_ne hc, hs]
    · rw [Function.update_of_ne hc]
      exact predResult_frame p d j hc hscratch

/-- Assembly interface exposing the changed word and unconstrained registers. -/
theorem pred_correct (p : Ports R S) (d : Data R S) (hs : d.stacks p.scratch = []) :
    ∃ (n : ℕ) (regs : Fin R → Bool) (word : List Bool),
      n ≤ 20 * ((d.stacks p.counter).length + 1) ∧
      StructuredCalls.Eval (predCmd p) n d
        ⟨regs, Function.update d.stacks p.counter word⟩ ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (d.stacks p.counter) - 1 ∧
      word.length ≤ (d.stacks p.counter).length := by
  refine ⟨predCost p d, (predResult p d).regs, (predResult p d).stacks p.counter,
    ?_, ?_, predResult_toNat p d, (predResult_length p d).le⟩
  · have h := predCost_le p d
    omega
  · have heq : predResult p d =
        ⟨(predResult p d).regs,
          Function.update d.stacks p.counter ((predResult p d).stacks p.counter)⟩ :=
      CounterForPrograms.data_ext rfl (predResult_stacks p d hs)
    rw [← heq]
    exact pred_eval p d hs

@[simp] theorem size_predCmd (p : Ports R S) : StructuredCalls.size (predCmd p) = 22 := by
  simp [ StructuredCalls.size, StructuredProgram.size]

def program (p : Ports R S) (inputStack outputStack : Fin S) :=
  StructuredCalls.compiled (predCmd p) inputStack outputStack

theorem program_runs (p : Ports R S) (d : Data R S) (hs : d.stacks p.scratch = [])
    (inputStack outputStack : Fin S) :
    BitProgram.RunsIn (program p inputStack outputStack)
      (20 * ((d.stacks p.counter).length + 1))
      (d.withPC (some (program p inputStack outputStack).entry))
      ((predResult p d).withPC none) :=
  ⟨predCost p d + 1, predCost_le p d,
    StructuredCalls.compiled_halt_trace (pred_eval p d hs) inputStack outputStack⟩

end SubexponentialSAT.CounterPredProgram

end OAI.Algorithms
