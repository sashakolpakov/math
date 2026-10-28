import OAI.Analysis.HodgeTheory.Decomposition.SmoothFrozenExtension
import Mathlib.Analysis.InnerProductSpace.Basic
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver

/-! # Coefficient Extension -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.CoefficientExtension

noncomputable section

section

/-! A smooth strictly elliptic coefficient has a genuine bounded Lipschitz extension preserving a positive lower bound. -/

open Filter
open scoped ContDiff _root_.Topology
open OAI.Analysis.HodgeTheory.Decomposition.SmoothFrozenExtension.Constructions

section Perturbation
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem real_inner_operator_lower_perturbation (A B : F →L[ℝ] F) (c ε : ℝ)
    (hclose : ‖A - B‖ ≤ ε) (v : F) (hA : c * ‖v‖ ^ 2 ≤ inner ℝ (A v) v) :
    (c - ε) * ‖v‖ ^ 2 ≤ inner ℝ (B v) v := by
  have hnorm : ‖(A - B) v‖ ≤ ε * ‖v‖ :=
    ((A - B).le_opNorm v).trans (mul_le_mul_of_nonneg_right hclose (norm_nonneg v))
  have hinner : inner ℝ ((A - B) v) v ≤ ε * ‖v‖ ^ 2 := by
    calc
      _ ≤ ‖(A - B) v‖ * ‖v‖ := real_inner_le_norm _ _
      _ ≤ (ε * ‖v‖) * ‖v‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg v)
      _ = _ := by ring
  rw [_root_.sub_apply, inner_sub_left] at hinner
  nlinarith only [hA, hinner]

end Perturbation

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem exists_positive_coefficient_extension {U : Set E} (hU : IsOpen U)
    (A : E → F →L[ℝ] F) (hA : ContDiffOn ℝ ∞ A U) {z : E} (hz : z ∈ U)
    (c : ℝ) (hc : 0 < c) (hpos : ∀ v : F, c * ‖v‖ ^ 2 ≤ inner ℝ (A z v) v) :
    ∃ B : E → F →L[ℝ] F, B =ᶠ[𝓝 z] A ∧ ContDiff ℝ ∞ B ∧
      HasCompactSupport (fun x => B x - A z) ∧
      (∃ C : ℝ, ∀ x, ‖B x‖ ≤ C) ∧ (∃ L : NNReal, LipschitzWith L B) ∧
      ∀ x v, (c / 2) * ‖v‖ ^ 2 ≤ inner ℝ (B x v) v := by
  obtain ⟨B, hlocal, hsmooth, hcompact, hclose, hbound, hLip⟩ :=
    OAI.Analysis.HodgeTheory.Decomposition.SmoothFrozenExtension.Constructions.exists_smooth_frozen_extension hU A hA hz (half_pos hc)
  refine ⟨B, hlocal, hsmooth, hcompact, hbound, hLip, fun x v => ?_⟩
  have he : ‖A z - B x‖ ≤ c / 2 := by rw [norm_sub_rev]; exact hclose x
  have hp := real_inner_operator_lower_perturbation (A z) (B x) c (c / 2) he v (hpos v)
  have hr : c - c / 2 = c / 2 := by ring
  exact Eq.mp (congrArg (fun r : ℝ => r * ‖v‖ ^ 2 ≤ inner ℝ (B x v) v) hr) hp

end

/-! Pointwise positive bounded coefficients give the required integrated coercivity for all genuine L² fields and all spatial translations. -/

open _root_.MeasureTheory
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem positive_coefficient_translated_integral (A : E → F →L[ℝ] F)
    (hA : Continuous A) (C c : ℝ) (hC : ∀ x, ‖A x‖ ≤ C)
    (hc : ∀ x v, c * ‖v‖ ^ 2 ≤ inner ℝ (A x v) v)
    (y : E) (u : Lp F 2 (volume : Measure E)) :
    c * ‖u‖ ^ 2 ≤ ∫ x, inner ℝ (A (x + y) (u x)) (u x) := by
  have hT : Continuous (fun x => A (x + y)) := hA.comp (continuous_id.add continuous_const)
  have hb : ∀ᵐ x ∂(volume : Measure E), ‖A (x + y)‖ ≤ C :=
    Filter.Eventually.of_forall (fun x => hC (x + y))
  have hp : ∀ᵐ x ∂(volume : Measure E), ∀ v : F, c * ‖v‖ * ‖v‖ ≤ inner ℝ (A (x + y) v) v := by
    apply Filter.Eventually.of_forall
    intro x v
    simpa only [pow_two, mul_assoc] using hc (x + y) v
  have h := ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_lower_bound (fun x => A (x + y)) hT.aestronglyMeasurable hb hp u
  rw [ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_apply] at h
  simpa only [pow_two, mul_assoc] using h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.CoefficientExtension
