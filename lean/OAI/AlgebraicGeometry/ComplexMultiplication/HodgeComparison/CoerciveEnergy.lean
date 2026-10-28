import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CompactEnergy
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-! # Coercive Energy -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveEnergy.CM.Construction

noncomputable section

/-! Quantitative Poincare bounds and variable-energy weak inversion. -/

open _root_.Module InnerProductSpace _root_.ContinuousLinearMap
open scoped InnerProduct

section

variable {𝕜 V H W : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [CompleteSpace W]

/-- The compact graph inclusion and zero derivative kernel give an actual
Poincare constant, including for the completed Sobolev domain. -/
theorem graphEnergy_poincare_bound (J : V →L[𝕜] H) (D : V →L[𝕜] W)
    (hJ : IsCompactOperator J) (hD : Function.Injective D)
    (hgraph : ∀ u v, inner 𝕜 u v = inner 𝕜 (J u) (J v) + inner 𝕜 (D u) (D v)) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : V, c * ‖u‖ ≤ ‖D u‖ := by
  let A := D.adjoint.comp D
  have hA : Function.Bijective A := CompactEnergy.CM.Construction.graphEnergy_bijective J D hJ hD hgraph
  let T : V ≃L[𝕜] V := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hA.injective) (LinearMap.range_eq_top.mpr hA.surjective)
  let C : ℝ := ‖T.symm.toContinuousLinearMap‖ * ‖D.adjoint‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound (u : V) : ‖u‖ ≤ C * ‖D u‖ := by
    calc
      ‖u‖ = ‖T.symm (D.adjoint (D u))‖ := by
        congr 1
        exact (T.symm_apply_apply u).symm
      _ ≤ ‖T.symm.toContinuousLinearMap‖ * ‖D.adjoint (D u)‖ := T.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖T.symm.toContinuousLinearMap‖ * (‖D.adjoint‖ * ‖D u‖) :=
        mul_le_mul_of_nonneg_left (D.adjoint.le_opNorm _) (norm_nonneg _)
      _ ≤ C * ‖D u‖ := by dsimp [C]; nlinarith [norm_nonneg (D u)]
  refine ⟨C⁻¹, inv_pos.mpr hC, fun u => ?_⟩
  rw [inv_mul_le_iff₀ hC]
  exact hbound u

end

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [CompleteSpace V] in
/-- A positive lower bound on derivative energy gives coercivity in the
Sobolev norm once the Poincare bound has been proved. -/
theorem derivative_energy_isCoercive (D : V →L[ℝ] W) (B : V →L[ℝ] V →L[ℝ] ℝ)
    {c a : ℝ} (hc : 0 < c) (ha : 0 < a)
    (hD : ∀ u : V, c * ‖u‖ ≤ ‖D u‖)
    (hB : ∀ u : V, a * ‖D u‖ * ‖D u‖ ≤ B u u) : IsCoercive B := by
  refine ⟨a * c ^ 2, mul_pos ha (sq_pos_of_pos hc), fun u => ?_⟩
  have hh := mul_le_mul (hD u) (hD u) (by positivity : 0 ≤ c * ‖u‖) (norm_nonneg (D u))
  calc
    a * c ^ 2 * ‖u‖ * ‖u‖ = a * ((c * ‖u‖) * (c * ‖u‖)) := by ring
    _ ≤ a * (‖D u‖ * ‖D u‖) := mul_le_mul_of_nonneg_left hh ha.le
    _ ≤ B u u := by simpa only [← mul_assoc] using hB u

/-- Lax--Milgram written directly as the weak equation for the continuous
bilinear energy and a bounded forcing functional. -/
theorem coercive_energy_weak_existsUnique (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : IsCoercive B) (ℓ : V →L[ℝ] ℝ) : ∃! u : V, ∀ v : V, B u v = ℓ v := by
  let T := hB.continuousLinearEquivOfBilin
  let r := (InnerProductSpace.toDual ℝ V).symm ℓ
  refine ⟨T.symm r, ?_, ?_⟩
  · intro v
    rw [← hB.continuousLinearEquivOfBilin_apply]
    change inner ℝ (T (T.symm r)) v = ℓ v
    rw [T.apply_symm_apply]
    exact InnerProductSpace.toDual_symm_apply
  · intro u hu
    apply T.injective
    rw [T.apply_symm_apply]
    apply ext_inner_right ℝ
    intro v
    rw [hB.continuousLinearEquivOfBilin_apply, hu]
    exact InnerProductSpace.toDual_symm_apply.symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveEnergy.CM.Construction
