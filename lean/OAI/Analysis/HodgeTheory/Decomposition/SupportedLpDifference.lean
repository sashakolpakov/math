import OAI.Analysis.HodgeTheory.Decomposition.CoefficientLinearity
import OAI.Analysis.HodgeTheory.Decomposition.CoordinateLp

/-! # Supported Lp Difference -/

namespace OAI.Analysis.HodgeTheory.Decomposition.SupportedLpDifference.Constructions

noncomputable section

/-! Pairwise L² coordinate comparisons for supported manifold forms. -/

open _root_.MeasureTheory

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)
  {K : Set V.analyticSpace} (hK : IsCompact K) (hKe : K ⊆ e.source)

theorem supportedCoordinatesLp_sub
    (a b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (ha : ∀ x, x ∉ K → a x = 0) (hb : ∀ x, x ∉ K → b x = 0)
    (hab : ∀ x, x ∉ K → (a - b) x = 0) :
    CoordinateLp.Constructions.supportedCoordinatesLp V e he n hK hKe (a - b) hab =
      CoordinateLp.Constructions.supportedCoordinatesLp V e he n hK hKe a ha - CoordinateLp.Constructions.supportedCoordinatesLp V e he n hK hKe b hb := by
  apply Lp.ext
  filter_upwards [(CoordinateLp.Constructions.supportedEuclideanCoefficients_memLp V e he n hK hKe (a - b) hab).coeFn_toLp,
    (CoordinateLp.Constructions.supportedEuclideanCoefficients_memLp V e he n hK hKe a ha).coeFn_toLp,
    (CoordinateLp.Constructions.supportedEuclideanCoefficients_memLp V e he n hK hKe b hb).coeFn_toLp,
    Lp.coeFn_sub (CoordinateLp.Constructions.supportedCoordinatesLp V e he n hK hKe a ha)
      (CoordinateLp.Constructions.supportedCoordinatesLp V e he n hK hKe b hb)] with x hx hy hz ht
  rw [ht]
  change (CoordinateLp.Constructions.supportedEuclideanCoefficients_memLp V e he n hK hKe (a - b) hab).toLp _ x = _
  rw [hx]
  change _ = (CoordinateLp.Constructions.supportedEuclideanCoefficients_memLp V e he n hK hKe a ha).toLp _ x -
    (CoordinateLp.Constructions.supportedEuclideanCoefficients_memLp V e he n hK hKe b hb).toLp _ x
  rw [hy, hz]
  exact congrFun ((CoefficientLinearity.Constructions.supportedCoefficientLinear V e n).map_sub a.val b.val) x

variable [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

theorem supportedCoordinatesLp_dist_comparison :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a b : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
        (ha : ∀ x, x ∉ K → a x = 0) (hb : ∀ x, x ∉ K → b x = 0),
        dist (Form.Constructions.smoothToProjectiveL2 V n a) (Form.Constructions.smoothToProjectiveL2 V n b) ≤
          C * dist (CoordinateLp.Constructions.supportedCoordinatesLp V e he n hK hKe a ha)
            (CoordinateLp.Constructions.supportedCoordinatesLp V e he n hK hKe b hb) := by
  obtain ⟨C, hC, hbound⟩ := CoordinateLp.Constructions.projective_supported_coordinate_upper V e he n hK hKe
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, fun a b ha hb => ?_⟩
  have hab : ∀ x, x ∉ K → (a - b) x = 0 := by
    intro x hx
    change a x - b x = 0
    rw [ha x hx, hb x hx, sub_self]
  have h := hbound (a - b) hab
  rw [map_sub, supportedCoordinatesLp_sub V e he n hK hKe a b ha hb hab] at h
  simp only [dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg _))).mp
  rwa [mul_pow, Real.sq_sqrt hC.le]

end

end OAI.Analysis.HodgeTheory.Decomposition.SupportedLpDifference.Constructions
