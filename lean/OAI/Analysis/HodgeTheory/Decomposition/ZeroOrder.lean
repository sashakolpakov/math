import OAI.Analysis.HodgeTheory.Decomposition.RestrictedCoordinate
import OAI.Analysis.HodgeTheory.Decomposition.CoordinateLp

/-! # Zero Order -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ZeroOrder.Constructions

noncomputable section

/-! A supported order-zero operation with a proved coefficient bound is
bounded in the genuine manifold L² norm. -/

open _root_.MeasureTheory Set

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

omit he [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] in
theorem supported_coordinate_norm_integral (n : ℕ)
    {K : Set V.analyticSpace} (hK : IsCompact K) (hKe : K ⊆ e.source)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (ha : ∀ x, x ∉ K → a x = 0) :
    (∫ z, ‖SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n a.val z‖ ^ 2) =
      ∫ z in MeasureVolume.Constructions.chartCoordinateForward V e '' K, ‖EuclideanForms.Constructions.euclideanChartCoefficients V e n a.val z‖ ^ 2 := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := MeasureVolume.Constructions.chartCoordinateForward V e '' K)
    (fun z hz => by
      have hzero := image_eq_zero_of_notMem_tsupport (fun h => hz
        (SupportedCoordinates.Constructions.supportedEuclideanCoefficients_tsupport V e n a.val hK hKe ha h))
      rw [hzero, norm_zero, zero_pow (by decide : 2 ≠ 0)])]
  apply setIntegral_congr_fun (SupportedCoordinates.Constructions.chartCoordinateForward_compact V e hK hKe).measurableSet
  rintro _ ⟨x, hx, rfl⟩
  dsimp only
  rw [SupportedCoordinates.Constructions.supportedEuclideanCoefficients_eq V e n a.val (MeasureVolume.Constructions.chartCoordinateForward_mem V e x (hKe hx))]

theorem projective_supported_zeroOrder_bound (n m : ℕ)
    {K : Set V.analyticSpace} (hK : IsCompact K) (hKe : K ⊆ e.source)
    (A : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n →
      DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace m)
    (hA : ∀ a x, x ∉ K → A a x = 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hcoeff : ∀ a z, z ∈ MeasureVolume.Constructions.chartCoordinateForward V e '' K →
      ‖EuclideanForms.Constructions.euclideanChartCoefficients V e m (A a).val z‖ ≤ C * ‖EuclideanForms.Constructions.euclideanChartCoefficients V e n a.val z‖) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a,
      ‖Form.Constructions.smoothToProjectiveL2 V m (A a)‖ ≤ B * ‖Form.Constructions.smoothToProjectiveL2 V n a‖ := by
  obtain ⟨B₀, hB₀, hnorm₀⟩ := RestrictedCoordinate.Constructions.projective_restricted_coordinate_norm_bound V e he n hK hKe
  obtain ⟨B₁, hB₁, hnorm₁⟩ := CoordinateLp.Constructions.projective_supported_coordinate_upper V e he m hK hKe
  let B := Real.sqrt (B₁ * C ^ 2 * B₀)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  refine ⟨B, hB, fun a => ?_⟩
  let L := MeasureVolume.Constructions.chartCoordinateForward V e '' K
  have hL : IsCompact L := SupportedCoordinates.Constructions.chartCoordinateForward_compact V e hK hKe
  have hLU : L ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := by
    rintro _ ⟨x, hx, rfl⟩
    exact MeasureVolume.Constructions.chartCoordinateForward_mem V e x (hKe hx)
  have hi (k : ℕ) (b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace k) :
      IntegrableOn (fun z => ‖EuclideanForms.Constructions.euclideanChartCoefficients V e k b.val z‖ ^ 2) L volume :=
    (((EuclideanForms.Constructions.euclideanChartCoefficients_smooth V e he k b).continuousOn.mono hLU).norm.pow 2).integrableOn_compact hL
  have hlocal : (∫ z in L, ‖EuclideanForms.Constructions.euclideanChartCoefficients V e m (A a).val z‖ ^ 2) ≤
      C ^ 2 * ∫ z in L, ‖EuclideanForms.Constructions.euclideanChartCoefficients V e n a.val z‖ ^ 2 := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on (hi m (A a)) ((hi n a).const_mul (C ^ 2)) hL.measurableSet
    intro z hz
    have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mpr (hcoeff a z hz)
    simpa only [mul_pow] using hs
  have h₁ := hnorm₁ (A a) (hA a)
  rw [CoordinateLp.Constructions.supportedCoordinatesLp_norm_sq, supported_coordinate_norm_integral V e m hK hKe (A a) (hA a)] at h₁
  have hsq := h₁.trans (mul_le_mul_of_nonneg_left
    (hlocal.trans (mul_le_mul_of_nonneg_left (hnorm₀ a) (sq_nonneg C))) hB₁.le)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ B₁ * C ^ 2 * B₀)]
  exact hsq.trans_eq (by ring)

end

end OAI.Analysis.HodgeTheory.Decomposition.ZeroOrder.Constructions
