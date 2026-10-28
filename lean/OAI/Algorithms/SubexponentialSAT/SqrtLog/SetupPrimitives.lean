import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpParameterProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticSchedule

namespace OAI.Algorithms

/-! Actual fixed bit programs for the two logarithmic setup quantities.
Input and output numbers are arbitrary padded little-endian words. -/
namespace SubexponentialSAT.SqrtLog.Setup

open BitProgram StructuredCalls
open CounterPrograms (value ripple)

abbrev Data := StructuredProgram.State 3 3
abbrev io (xs : List Bool) : Data := StructuredProgram.ioState 0 xs

def incrementPorts : Fin 2 → Fin 3 := ![0, 1]

theorem incrementPorts_injective : Function.Injective incrementPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [incrementPorts]

abbrev increment : Cmd 3 3 :=
  .call (ProgramLinking.liftProgram (CounterPrograms.rippleProgram true) id incrementPorts)

theorem increment_eval (xs : List Bool) :
    Eval increment (CounterPrograms.rippleCost true xs + 1) (io xs) (io (ripple true xs)) := by
  have he := eval_call_lifted (CounterPrograms.rippleProgram true) id incrementPorts
    (io xs) Function.injective_id incrementPorts_injective
    (a := StructuredProgram.ioState (0 : Fin 2) xs)
    (b := StructuredProgram.ioState (0 : Fin 2) (ripple true xs))
    (CounterPrograms.ripple_terminal_trace true xs)
  have ha : embedState id incrementPorts (io xs)
      (StructuredProgram.ioState (0 : Fin 2) xs) = io xs := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id incrementPorts_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
  have hb : embedState id incrementPorts (io xs)
      (StructuredProgram.ioState (0 : Fin 2) (ripple true xs)) = io (ripple true xs) := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id incrementPorts_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;> simp_all [incrementPorts, io, StructuredProgram.ioState,
        Fin.exists_fin_succ]
  change Eval increment _ (embedState id incrementPorts (io xs)
    (StructuredProgram.ioState (0 : Fin 2) xs))
    (embedState id incrementPorts (io xs)
      (StructuredProgram.ioState (0 : Fin 2) (ripple true xs))) at he
  simpa only [ha, hb] using he

/-- `k` is fixed syntax, not a natural-number machine instruction. -/
def addConst : ℕ → Cmd 3 3
  | 0 => .base .skip
  | k + 1 => .seq (addConst k) increment

theorem addConst_eval (k : ℕ) (xs : List Bool) :
    ∃ output t, value output = value xs + k ∧ output.length ≤ xs.length + k ∧
      t ≤ 8 * k * (xs.length + k + 1) ∧ Eval (addConst k) t (io xs) (io output) := by
  induction k with
  | zero => exact ⟨xs, 0, by simp, by simp, by simp, .base (.skip _)⟩
  | succ k ih =>
    obtain ⟨ys, t, hv, hl, ht, he⟩ := ih
    refine ⟨ripple true ys, t + (CounterPrograms.rippleCost true ys + 1), ?_, ?_, ?_,
      he.seq (increment_eval ys)⟩
    · rw [CounterPrograms.value_increment, hv]
      omega
    · exact (CounterPrograms.ripple_length_le true ys).trans (by omega)
    · have hc := CounterPrograms.rippleCost_le true ys
      nlinarith

abbrev logarithm : Cmd 3 3 := .call SubexpParameterProgram.logProgram

theorem logarithm_eval (xs : List Bool) :
    ∃ output t, value output = Nat.log2 (value xs) ∧ output.length ≤ xs.length ∧
      t ≤ SubexpParameterProgram.logBound xs.length ∧
      Eval logarithm t (io xs) (io output) := by
  obtain ⟨output, hv, hl, t, ht, he⟩ := SubexpParameterProgram.log_correct xs
  exact ⟨output, t, hv, hl, ht, .call _ he⟩

/-- The floor binary logarithm plus one, with zero mapped to one. -/
abbrev logSucc : Cmd 3 3 := .seq logarithm increment

theorem logSucc_eval (xs : List Bool) :
    ∃ output t, value output = Nat.log2 (value xs) + 1 ∧ output.length ≤ xs.length + 1 ∧
      t ≤ 32 * (xs.length + 1)^2 ∧ Eval logSucc t (io xs) (io output) := by
  obtain ⟨ys, t, hv, hl, ht, he⟩ := logarithm_eval xs
  refine ⟨ripple true ys, t + (CounterPrograms.rippleCost true ys + 1), ?_, ?_, ?_,
    he.seq (increment_eval ys)⟩
  · rw [CounterPrograms.value_increment, hv]
  · exact (CounterPrograms.ripple_length_le true ys).trans (by omega)
  · have hc := CounterPrograms.rippleCost_le true ys
    rw [SubexpParameterProgram.logBound_eq] at ht
    nlinarith

/-- Sixteen explicit increments, followed by the actual log-plus-one program. -/
abbrev computeL : Cmd 3 3 := .seq (addConst 16) logSucc

theorem computeL_eval (xs : List Bool) :
    ∃ output t, value output = Asymptotic.L (value xs) ∧
      output.length ≤ xs.length + 17 ∧ t ≤ 16384 * (xs.length + 1)^2 ∧
      Eval computeL t (io xs) (io output) := by
  obtain ⟨ys, t, hv, hl, ht, he⟩ := addConst_eval 16 xs
  obtain ⟨zs, u, hz, hzl, hu, hf⟩ := logSucc_eval ys
  refine ⟨zs, t + u, ?_, by omega, ?_, he.seq hf⟩
  · simpa [Asymptotic.L, hv] using hz
  · nlinarith

def computeLProgram := compiled computeL 0 0

theorem computeL_runs (xs : List Bool) :
    ∃ output, value output = Asymptotic.L (value xs) ∧
      output.length ≤ xs.length + 17 ∧
      RunsIn computeLProgram (16385 * (xs.length + 1)^2)
        (initial computeLProgram xs) (terminal computeLProgram output) := by
  obtain ⟨output, t, hv, hl, ht, he⟩ := computeL_eval xs
  refine ⟨output, hv, hl, t + 1, by nlinarith, ?_⟩
  exact compiled_io_trace 0 0 he

def logSuccProgram := compiled logSucc 0 0

theorem logSucc_runs (xs : List Bool) :
    ∃ output, value output = Nat.log2 (value xs) + 1 ∧ output.length ≤ xs.length + 1 ∧
      RunsIn logSuccProgram (33 * (xs.length + 1)^2)
        (initial logSuccProgram xs) (terminal logSuccProgram output) := by
  obtain ⟨output, t, hv, hl, ht, he⟩ := logSucc_eval xs
  exact ⟨output, hv, hl, t + 1, by nlinarith, compiled_io_trace 0 0 he⟩

end SubexponentialSAT.SqrtLog.Setup

namespace SubexponentialSAT.SqrtLog.Setup

open CounterPrograms (value)

/-- The numerical search fuel itself is linear in the original bit length. -/
theorem L_le_wordLength (xs : List Bool) : Asymptotic.L (value xs) ≤ xs.length+5 := by
  have hv := SubexpParameterProgram.value_lt_two_pow_length xs
  have hp := Nat.two_pow_pos xs.length
  have hb : value xs+16 < 2^(xs.length+5) := by
    rw [pow_add]
    norm_num
    omega
  have hl := (Nat.log2_lt (show value xs+16 ≠ 0 by omega)).mpr hb
  dsimp [Asymptotic.L]
  omega

end SubexponentialSAT.SqrtLog.Setup

end OAI.Algorithms
