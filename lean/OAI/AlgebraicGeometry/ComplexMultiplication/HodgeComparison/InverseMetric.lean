import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricBounds
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-! # Inverse Metric -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.InverseMetric.CM.Construction

noncomputable section

/-! Invertibility and smooth inversion of positive metric coefficients. -/

open scoped ContDiff
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

def realBilinearOperator : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E) :=
  ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) E
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap

omit [ProperSpace E] in
theorem realBilinearOperator_apply (B : E →L[ℝ] E →L[ℝ] ℝ) (u v : E) :
    inner ℝ (realBilinearOperator B u) v = B u v :=
  InnerProductSpace.continuousLinearMapOfBilin_apply B u v

omit [CompleteSpace E] in
theorem positive_bilinear_isCoercive (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) : IsCoercive B := by
  obtain ⟨c, hc, h⟩ := MetricBounds.CM.Construction.positive_bilinear_uniform_lower_bound (fun _ : Unit => B)
    (K := Set.univ) isCompact_univ continuousOn_const (fun _ _ => hpos)
  exact ⟨c, hc, fun u => h () (Set.mem_univ ()) u⟩

theorem positive_bilinear_operator_isInvertible (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) : (realBilinearOperator B).IsInvertible := by
  refine ⟨(positive_bilinear_isCoercive B hpos).continuousLinearEquivOfBilin, ?_⟩
  rfl

def inverseBilinearForm (B : E →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (realBilinearOperator B).inverse

omit [ProperSpace E] in
theorem inverseBilinearForm_apply (B : E →L[ℝ] E →L[ℝ] ℝ) (u v : E) :
    inverseBilinearForm B u v = inner ℝ ((realBilinearOperator B).inverse u) v := rfl

theorem inverseBilinearForm_positive (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) (u : E) (hu : u ≠ 0) :
    0 < inverseBilinearForm B u u := by
  let A := realBilinearOperator B
  have hA : A.IsInvertible := positive_bilinear_operator_isInvertible B hpos
  have hn : A.inverse u ≠ 0 := by
    intro h
    have hh := hA.self_apply_inverse u
    rw [h, map_zero] at hh
    exact hu hh.symm
  rw [inverseBilinearForm_apply]
  change 0 < inner ℝ (A.inverse u) u
  have heq : inner ℝ (A.inverse u) u = B (A.inverse u) (A.inverse u) := by
    calc
      inner ℝ (A.inverse u) u = inner ℝ (A.inverse u) (A (A.inverse u)) :=
        congrArg (fun z => inner ℝ (A.inverse u) z) (hA.self_apply_inverse u).symm
      _ = B (A.inverse u) (A.inverse u) := by
        rw [real_inner_comm]
        exact realBilinearOperator_apply B _ _
  rw [heq]
  exact hpos _ hn

theorem inverseBilinearForm_symmetric (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) (hsym : ∀ u v : E, B u v = B v u)
    (u v : E) : inverseBilinearForm B u v = inverseBilinearForm B v u := by
  let A := realBilinearOperator B
  have hA : A.IsInvertible := positive_bilinear_operator_isInvertible B hpos
  have heq (x y : E) : inverseBilinearForm B x y = B (A.inverse y) (A.inverse x) := by
    rw [inverseBilinearForm_apply]
    change inner ℝ (A.inverse x) y = _
    calc
      inner ℝ (A.inverse x) y = inner ℝ (A.inverse x) (A (A.inverse y)) :=
        congrArg (fun z => inner ℝ (A.inverse x) z) (hA.self_apply_inverse y).symm
      _ = B (A.inverse y) (A.inverse x) := by
        rw [real_inner_comm]
        exact realBilinearOperator_apply B _ _
  rw [heq, heq, hsym]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem positive_bilinear_inverse_smoothOn (B : F → E →L[ℝ] E →L[ℝ] ℝ)
    {U : Set F} (hU : IsOpen U) (hB : ContDiffOn ℝ ∞ B U)
    (hpos : ∀ x ∈ U, ∀ u : E, u ≠ 0 → 0 < B x u u) :
    ContDiffOn ℝ ∞ (fun x => (realBilinearOperator (B x)).inverse) U := by
  have hlin := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := (∞ : ℕ∞ω))
    (E := E →L[ℝ] E →L[ℝ] ℝ) (F := E →L[ℝ] E) (realBilinearOperator (E := E))
  intro x hx
  have hcoeff : ContDiffAt ℝ ∞ (fun y => realBilinearOperator (B y)) x :=
    hlin.contDiffAt.comp x (hB.contDiffAt (hU.mem_nhds hx))
  exact ((positive_bilinear_operator_isInvertible (B x) (hpos x hx)).contDiffAt_map_inverse.comp
    x hcoeff).contDiffWithinAt

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.InverseMetric.CM.Construction
