import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Computation
import OAI.Algorithms.SubexponentialSAT.StackAdapter

namespace OAI.Algorithms

/-!
# Precise computational target of the subexponential SAT manuscript

The source is `source/subexponential-sat.pdf`, Theorem 1.  The input and
primitive transition model are unchanged from `SubexponentialSAT.Computation`.  Both
constants, the polynomial degree, and the finite machine are chosen before
the input size.  In particular the growing layout parameters cannot be
encoded as size-dependent advice in the machine.

This module defines the target and proves elementary closure and compiler
lemmas.  It does not assert that a solver satisfying the target exists.
-/

namespace SubexponentialSAT.SubexpComputation

open _root_.OAI.Algorithms.SubexponentialSAT.Computation

noncomputable section

/-- The positive base-two iterated logarithm used in Theorem 1, including its
specified shift at small inputs. -/
def logLog (n : ℕ) : ℝ :=
  Real.logb 2 (Real.logb 2 ((n : ℝ) + 16))

/-- The actual subexponential scale, not a free exponent function. -/
def scale (n : ℕ) : ℝ := (n : ℝ) / logLog n

private theorem logb_two_four : Real.logb 2 4 = 2 := by
  have h := Real.logb_pow 2 2 2
  norm_num at h ⊢
  exact h

private theorem logb_two_sixteen : Real.logb 2 16 = 4 := by
  have h := Real.logb_pow 2 2 4
  norm_num at h ⊢
  exact h

theorem two_le_logLog (n : ℕ) : 2 ≤ logLog n := by
  have hinner : (4 : ℝ) ≤ Real.logb 2 ((n : ℝ) + 16) := by
    calc
      (4 : ℝ) = Real.logb 2 16 := logb_two_sixteen.symm
      _ ≤ Real.logb 2 ((n : ℝ) + 16) :=
        Real.logb_le_logb_of_le (by norm_num) (by norm_num)
          (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  calc
    (2 : ℝ) = Real.logb 2 4 := logb_two_four.symm
    _ ≤ Real.logb 2 (Real.logb 2 ((n : ℝ) + 16)) :=
      Real.logb_le_logb_of_le (by norm_num) (by norm_num) hinner

theorem logLog_pos (n : ℕ) : 0 < logLog n :=
  lt_of_lt_of_le (by norm_num) (two_le_logLog n)

theorem scale_nonneg (n : ℕ) : 0 ≤ scale n :=
  div_nonneg (Nat.cast_nonneg n) (logLog_pos n).le

@[simp] theorem scale_zero : scale 0 = 0 := by simp [scale]

theorem scale_le_half (n : ℕ) : scale n ≤ (n : ℝ) / 2 := by
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg n) (by norm_num) (two_le_logLog n)

/-- The two constants are independent: the outer multiplicative constant
and the constant in the exponent can both depend on the fixed clause width. -/
def runtimeBound (constant exponentConstant : ℝ) (degree inputBits numVars : ℕ) : ℝ :=
  constant * ((inputBits : ℝ) + 1) ^ degree *
    (2 : ℝ) ^ (exponentConstant * scale numVars)

theorem runtimeBound_nonneg {constant : ℝ} (hc : 0 ≤ constant)
    (exponentConstant : ℝ) (degree inputBits numVars : ℕ) :
    0 ≤ runtimeBound constant exponentConstant degree inputBits numVars := by
  unfold runtimeBound
  positivity

theorem runtimeBound_mono_exponent {constant a b : ℝ} (hc : 0 ≤ constant)
    (hab : a ≤ b) (degree inputBits numVars : ℕ) :
    runtimeBound constant a degree inputBits numVars ≤
      runtimeBound constant b degree inputBits numVars := by
  apply mul_le_mul_of_nonneg_left
  · apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact mul_le_mul_of_nonneg_right hab (scale_nonneg numVars)
  · exact mul_nonneg hc (pow_nonneg (by positivity) degree)

theorem runtimeBound_mul_constant (factor constant exponentConstant : ℝ)
    (degree inputBits numVars : ℕ) :
    runtimeBound (factor * constant) exponentConstant degree inputBits numVars =
      factor * runtimeBound constant exponentConstant degree inputBits numVars := by
  unfold runtimeBound
  ring

/-- A fixed-degree polynomial slowdown preserves the target exponential
scale.  The degree must be fixed before the input size. -/
theorem runtimeBound_pow (constant exponentConstant : ℝ)
    (degree inputBits numVars power : ℕ) :
    runtimeBound constant exponentConstant degree inputBits numVars ^ power =
      runtimeBound (constant ^ power) ((power : ℝ) * exponentConstant)
        (degree * power) inputBits numVars := by
  unfold runtimeBound
  rw [mul_pow, mul_pow, ← pow_mul, ← Real.rpow_mul_natCast (by norm_num)]
  congr 2
  ring

/-- Sequential input handling and a fixed polynomial overhead may be added
to a source runtime without changing the asymptotic class. -/
theorem one_le_runtimeBound {constant exponentConstant : ℝ}
    (hc : 1 ≤ constant) (ha : 0 ≤ exponentConstant)
    (degree inputBits numVars : ℕ) :
    1 ≤ runtimeBound constant exponentConstant degree inputBits numVars := by
  unfold runtimeBound
  apply one_le_mul_of_one_le_of_one_le
  · exact one_le_mul_of_one_le_of_one_le hc
      (one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) inputBits; linarith))
  · exact Real.one_le_rpow (by norm_num) (mul_nonneg ha (scale_nonneg numVars))

/-- One fixed finite primitive machine reads the concrete raw CNF encoding,
returns a correct answer, and has an actual bounded transition trace. -/
def DecidesWithBound (machine : PrimitiveMachine) (width : ℕ)
    (constant exponentConstant : ℝ) (degree : ℕ) : Prop :=
  ∀ (n : ℕ) (F : SAT.CNF (Fin n)), SAT.WidthAtMost width F →
    ∃ (answer : Bool) (time : ℕ),
      machine.OutputsInTime (Encoding.encodeCNF F) answer time ∧
      (answer = true ↔ SAT.Satisfiable F) ∧
      (time : ℝ) ≤ runtimeBound constant exponentConstant degree
        (Encoding.formulaBitLength F) n

/-- The same contract at the finite-alphabet stack-machine level.  A separate
proved compiler, rather than an identification of macrosteps with bit steps,
is used below to obtain the primitive contract. -/
def MacrostepDecidesWithBound (machine : BitMachine) (width : ℕ)
    (constant exponentConstant : ℝ) (degree : ℕ) : Prop :=
  ∀ (n : ℕ) (F : SAT.CNF (Fin n)), SAT.WidthAtMost width F →
    ∃ (answer : Bool) (time : ℕ),
      machine.OutputsInTime (Encoding.encodeCNF F) [answer] time ∧
      (answer = true ↔ SAT.Satisfiable F) ∧
      (time : ℝ) ≤ runtimeBound constant exponentConstant degree
        (Encoding.formulaBitLength F) n

/-- Uniformity is expressed by the existential machine preceding every input
in `DecidesWithBound`. -/
def Feasible (width : ℕ) : Prop :=
  ∃ (machine : PrimitiveMachine) (constant exponentConstant : ℝ) (degree : ℕ),
    0 < constant ∧ 0 < exponentConstant ∧ 0 < degree ∧
      DecidesWithBound machine width constant exponentConstant degree

def MacrostepFeasible (width : ℕ) : Prop :=
  ∃ (machine : BitMachine) (constant exponentConstant : ℝ) (degree : ℕ),
    0 < constant ∧ 0 < exponentConstant ∧ 0 < degree ∧
      MacrostepDecidesWithBound machine width constant exponentConstant degree

/-- The full statement of Theorem 1 of `subexponential-sat.pdf`.
No inhabitant is supplied merely by this definition. -/
def MainTheorem : Prop := ∀ width : ℕ, 3 ≤ width → Feasible width

theorem primitive_bound_of_simulation {source : BitMachine}
    {target : PrimitiveMachine} {overhead width degree : ℕ}
    {constant exponentConstant : ℝ}
    (sim : MacroToPrimitiveSimulation source target overhead)
    (h : MacrostepDecidesWithBound source width constant exponentConstant degree) :
    DecidesWithBound target width ((overhead : ℝ) * constant) exponentConstant degree := by
  intro n F hF
  obtain ⟨answer, time, hrun, hcorrect, htime⟩ := h n F hF
  refine ⟨answer, overhead * time, sim.outputs hrun, hcorrect, ?_⟩
  rw [Nat.cast_mul, runtimeBound_mul_constant]
  exact mul_le_mul_of_nonneg_left htime (Nat.cast_nonneg overhead)

theorem feasible_of_simulation {source : BitMachine}
    {target : PrimitiveMachine} {overhead width degree : ℕ}
    {constant exponentConstant : ℝ}
    (sim : MacroToPrimitiveSimulation source target overhead)
    (ho : 0 < overhead) (hc : 0 < constant) (ha : 0 < exponentConstant)
    (hd : 0 < degree)
    (h : MacrostepDecidesWithBound source width constant exponentConstant degree) :
    Feasible width := by
  refine ⟨target, (overhead : ℝ) * constant, exponentConstant, degree,
    mul_pos (Nat.cast_pos.mpr ho) hc, ha, hd, ?_⟩
  exact primitive_bound_of_simulation sim h

/-- The already checked finite-alphabet compiler supplies all simulation
premises, so a complete macrostep solver would suffice for Theorem 1. -/
theorem macrostep_to_primitive {width : ℕ}
    (h : MacrostepFeasible width) : Feasible width := by
  obtain ⟨machine, constant, exponentConstant, degree, hc, ha, hd, hbound⟩ := h
  exact feasible_of_simulation (StackAdapter.simulation machine)
    (StackAdapter.overhead_pos machine) hc ha hd hbound

theorem width_antitone {width width' : ℕ} (hw : width ≤ width')
    (h : Feasible width') : Feasible width := by
  obtain ⟨machine, constant, exponentConstant, degree, hc, ha, hd, hdec⟩ := h
  refine ⟨machine, constant, exponentConstant, degree, hc, ha, hd, ?_⟩
  intro n F hF
  exact hdec n F (fun C hC => (hF C hC).trans hw)

end

end SubexponentialSAT.SubexpComputation

end OAI.Algorithms
