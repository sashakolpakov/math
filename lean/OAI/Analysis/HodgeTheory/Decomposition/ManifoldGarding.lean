import OAI.Analysis.HodgeTheory.Decomposition.LocalGarding
import OAI.Analysis.HodgeTheory.Decomposition.SupportedSchwartz
import OAI.Analysis.HodgeTheory.Decomposition.CoordinateLp

/-! # Manifold Garding -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ManifoldGarding.Constructions

noncomputable section

/-! The local first-order estimate expressed in the genuine manifold L²
norms of a form, its exterior derivative, and its constructed codifferential. -/

open _root_.MeasureTheory LineDeriv _root_.Metric
open scoped SchwartzMap BigOperators

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)

include he

theorem supportedEuclideanCoefficients_integral_bound
    {K : Set V.analyticSpace} (hK : IsCompact K) (hKe : K ⊆ e.source) :
    ∃ B : ℝ, 0 < B ∧ ∀ a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n,
      (∀ x, x ∉ K → a x = 0) →
      (∫ x, ‖SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n a.val x‖ ^ 2) ≤
        B * ‖Form.Constructions.smoothToProjectiveL2 V n a‖ ^ 2 := by
  obtain ⟨c, hc, hbound⟩ := CoordinateLp.Constructions.supportedCoordinatesLp_uniform_bound V e he n hK hKe
  refine ⟨c⁻¹, inv_pos.mpr hc, fun a ha => ?_⟩
  have h := hbound a ha
  rw [CoordinateLp.Constructions.supportedCoordinatesLp_norm_sq] at h
  have h' := mul_le_mul_of_nonneg_left h (inv_pos.mpr hc).le
  rwa [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at h'

theorem projectiveManifold_local_garding
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ r : ℝ, 0 < r ∧ closedBall z r ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e ∧
      ∀ (K : Set V.analyticSpace), IsCompact K → K ⊆ e.source →
        MeasureVolume.Constructions.chartCoordinateForward V e '' K ⊆ closedBall z r →
        ∃ C : ℝ, 0 < C ∧
          ∀ (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)),
            (∀ x, x ∉ K → a x = 0) →
            (∑ i : AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V, ∫ x,
              ‖fderiv ℝ (SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e (n + 1) a.val) x
                (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) i)‖ ^ 2) ≤
              C * (‖Form.Constructions.smoothToProjectiveL2 V (n + 1 + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a)‖ ^ 2 +
                ‖Form.Constructions.smoothToProjectiveL2 V n (AdjointAlgebra.Constructions.projectiveCodifferential V n a)‖ ^ 2 +
                ‖Form.Constructions.smoothToProjectiveL2 V (n + 1) a‖ ^ 2) := by
  obtain ⟨r, hr, hchart, C₀, hC₀, hlocal⟩ := LocalGarding.Constructions.projectiveLocal_garding V e n he z hz
  refine ⟨r, hr, hchart, fun K hK hKe hKball => ?_⟩
  obtain ⟨B₀, hB₀, hbound₀⟩ := supportedEuclideanCoefficients_integral_bound V e he (n + 1) hK hKe
  obtain ⟨B₁, hB₁, hbound₁⟩ := supportedEuclideanCoefficients_integral_bound V e he (n + 1 + 1) hK hKe
  obtain ⟨B₂, hB₂, hbound₂⟩ := supportedEuclideanCoefficients_integral_bound V e he n hK hKe
  let B := B₀ + B₁ + B₂
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨C₀ * B, mul_pos hC₀ hB, fun a ha => ?_⟩
  let u := SupportedSchwartz.Constructions.supportedCoordinatesSchwartz V e he (n + 1) hK hKe a ha
  have hu : HasCompactSupport u := SupportedCoordinates.Constructions.supportedEuclideanCoefficients_compact V e (n + 1) a.val hK hKe ha
  have hs : tsupport u ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e :=
    SupportedCoordinates.Constructions.supportedEuclideanCoefficients_tsupport_domain V e (n + 1) a.val hK hKe ha
  have hsub : tsupport u ⊆ closedBall z r :=
    (SupportedCoordinates.Constructions.supportedEuclideanCoefficients_tsupport V e (n + 1) a.val hK hKe ha).trans hKball
  have hg := hlocal u hu hsub hs
  have hd (x : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : FrozenFourier.Constructions.projectiveFrozenD V (n + 1) u x =
      SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e (n + 1 + 1) (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a).val x :=
    SupportedSchwartz.Constructions.supportedCoordinatesSchwartz_d V e he (n + 1) hK hKe a ha x
  have ht (x : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : LocalSchwartzDelta.Constructions.projectiveLocalDeltaSchwartz V e n he u hu hs x =
      SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n (AdjointAlgebra.Constructions.projectiveCodifferential V n a).val x :=
    SupportedSchwartz.Constructions.supportedCoordinatesSchwartz_delta V e he n hK hKe a ha x
  simp_rw [hd, ht, SchwartzMap.lineDerivOp_apply_eq_fderiv] at hg
  have hd0 : ∀ x, x ∉ K → DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a x = 0 :=
    fun _ hx => SupportedCoordinates.Constructions.manifold_d_zero_off_closed V (n + 1) a hK.isClosed ha hx
  have ht0 : ∀ x, x ∉ K → AdjointAlgebra.Constructions.projectiveCodifferential V n a x = 0 :=
    fun _ hx => CodifferentialSupport.Constructions.projectiveCodifferential_zero_off_closed V n a hK.isClosed ha hx
  have h₀ := hbound₀ a ha
  have h₁ := hbound₁ (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) hd0
  have h₂ := hbound₂ (AdjointAlgebra.Constructions.projectiveCodifferential V n a) ht0
  have hB₀' : B₀ ≤ B := by dsimp [B]; linarith
  have hB₁' : B₁ ≤ B := by dsimp [B]; linarith
  have hB₂' : B₂ ≤ B := by dsimp [B]; linarith
  have hsum := add_le_add (add_le_add
    (h₁.trans (mul_le_mul_of_nonneg_right hB₁' (sq_nonneg _)))
    (h₂.trans (mul_le_mul_of_nonneg_right hB₂' (sq_nonneg _))))
    (h₀.trans (mul_le_mul_of_nonneg_right hB₀' (sq_nonneg _)))
  have hfinal := hg.trans (mul_le_mul_of_nonneg_left hsum hC₀.le)
  convert hfinal using 1 <;> first | rfl | ring

end

end OAI.Analysis.HodgeTheory.Decomposition.ManifoldGarding.Constructions
