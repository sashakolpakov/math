import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EllipticDifferenceEstimate

/-! # Cutoff Difference Bounds -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferenceBounds.CM.Construction

noncomputable section

/-! The flux created by a smooth cutoff has bounded spatial difference
quotients, including after application of Lipschitz metric coefficients. -/

open _root_.MeasureTheory
open scoped SchwartzMap LineDeriv

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

theorem realL2Difference_synthesis (m : E) (t : ℝ)
    (u v : PiLp 2 (fun _ : ι => Lp ℂ 2 (volume : Measure E)))
    (h : ∀ i, v i = DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t (u i)) :
    DifferenceProduct.CM.Construction.realL2Difference m t (LpComponents.CM.Construction.lpOrthonormalSynthesis (EuclideanSpace.basisFun ι ℂ) u) =
      LpComponents.CM.Construction.lpOrthonormalSynthesis (EuclideanSpace.basisFun ι ℂ) v := by
  have hc : ∀ᵐ x ∂(volume : Measure E), ∀ i,
      (v i) x = (t : ℂ)⁻¹ * ((u i) (x + t • m) - (u i) x) := by
    apply ae_all_iff.mpr
    intro i
    rw [h i]
    exact DifferenceQuotients.CM.Construction.l2DifferenceQuotient_coe m t (u i)
  apply Lp.ext
  filter_upwards [DifferenceProduct.CM.Construction.realL2Difference_coe m t (LpComponents.CM.Construction.lpOrthonormalSynthesis (EuclideanSpace.basisFun ι ℂ) u),
    LpComponents.CM.Construction.lpOrthonormalSynthesis_coe (EuclideanSpace.basisFun ι ℂ) u,
    (measurePreserving_add_right volume (t • m)).quasiMeasurePreserving.ae
      (LpComponents.CM.Construction.lpOrthonormalSynthesis_coe (EuclideanSpace.basisFun ι ℂ) u),
    LpComponents.CM.Construction.lpOrthonormalSynthesis_coe (EuclideanSpace.basisFun ι ℂ) v, hc]
    with x hd h0 ht hv hx
  rw [hd, h0, ht, hv, ← Finset.sum_sub_distrib, Finset.smul_sum]
  simp only [hx, ← sub_smul, ← Complex.coe_smul, Complex.ofReal_inv, smul_smul]

theorem synthesis_difference_bounded (m : E)
    (u : PiLp 2 (fun _ : ι => Lp ℂ 2 (volume : Measure E)))
    (h : ∀ i, ∃ B : ℝ, ∀ t, ‖DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t (u i)‖ ≤ B) :
    ∃ B : ℝ, ∀ t, ‖DifferenceProduct.CM.Construction.realL2Difference m t
      (LpComponents.CM.Construction.lpOrthonormalSynthesis (EuclideanSpace.basisFun ι ℂ) u)‖ ≤ B := by
  classical
  choose B hB using h
  let C : ℝ := ∑ i, max (B i) 0
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => le_max_right _ _)
  let T := (PiLp.continuousLinearEquiv 2 ℂ
    (fun _ : ι => Lp ℂ 2 (volume : Measure E))).symm.toContinuousLinearMap
  refine ⟨‖T‖ * C, fun t => ?_⟩
  let v := T (fun i => DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t (u i))
  rw [realL2Difference_synthesis m t u v (fun _ => rfl)]
  have hs : ‖LpComponents.CM.Construction.lpOrthonormalSynthesis (EuclideanSpace.basisFun ι ℂ) v‖ = ‖v‖ :=
    (LpComponents.CM.Construction.lpOrthonormalSynthesisIsometry (EuclideanSpace.basisFun ι ℂ)).norm_map v
  rw [hs]
  apply (T.le_opNorm _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg T)
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro i
  exact (hB i t).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun j _ => le_max_right (B j) 0) (Finset.mem_univ i)))

theorem cutoffGradient_difference_bounded (b : OrthonormalBasis ι ℝ E)
    (g : 𝓢(E, ℂ)) (u : Lp ℂ 2 (volume : Measure E)) (m : E) :
    ∃ B : ℝ, ∀ t, ‖DifferenceProduct.CM.Construction.realL2Difference m t (CutoffDifferential.CM.Construction.cutoffGradientMultiply b g
      (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u))‖ ≤ B := by
  apply synthesis_difference_bounded m
  intro i
  refine ⟨‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ *
    ((2 * Real.pi * ‖m‖) * ‖SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 (∂_{b i} g : 𝓢(E, ℂ)) u‖), fun t => ?_⟩
  change ‖DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
    CutoffDifferential.CM.Construction.schwartzL2Multiply (∂_{b i} g : 𝓢(E, ℂ))
      (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u))‖ ≤ _
  rw [map_smul, norm_smul,
    ← CutoffDifferential.CM.Construction.sobolevCutoffCLM_embedding]
  exact mul_le_mul_of_nonneg_left (DifferenceBounds.CM.Construction.l2DifferenceQuotient_sobolev_bound m t _)
    (norm_nonneg _)

theorem boundedField_difference_bounded
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι) {L : NNReal}
    (hA : LipschitzWith L A) {C : ℝ} (hC : ∀ x, ‖A x‖ ≤ C)
    (q : Lp (EuclideanSpace ℂ ι) 2 (volume : Measure E)) (m : E)
    (hq : ∃ B : ℝ, ∀ t, ‖DifferenceProduct.CM.Construction.realL2Difference m t q‖ ≤ B) :
    ∃ B : ℝ, ∀ t, ‖DifferenceProduct.CM.Construction.realL2Difference m t (LpCoefficients.CM.Construction.boundedFieldLp A hA.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hC) q)‖ ≤ B := by
  obtain ⟨B, hB⟩ := hq
  have hC₀ : 0 ≤ C := (norm_nonneg (A 0)).trans (hC 0)
  let hAm := hA.continuous.aestronglyMeasurable (μ := (volume : Measure E))
  let hCm : ∀ᵐ x ∂(volume : Measure E), ‖A x‖ ≤ C := Filter.Eventually.of_forall hC
  refine ⟨C * B + ((L : ℝ) * ‖m‖) * ‖q‖, fun t => ?_⟩
  rw [DifferenceProduct.CM.Construction.realL2Difference_coefficient_product]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (EllipticDifferenceEstimate.CM.Construction.boundedFieldLp_norm_le_other _ (DifferenceProduct.CM.Construction.translatedCoefficient_measurable A hAm (t • m))
      (DifferenceProduct.CM.Construction.translatedCoefficient_bound A hCm (t • m)) (DifferenceProduct.CM.Construction.translatedCoefficient_bound A hCm (t • m))
      (DifferenceProduct.CM.Construction.realL2Difference m t q)).trans (mul_le_mul_of_nonneg_left (hB t) hC₀)
  · exact EllipticDifferenceEstimate.CM.Construction.boundedFieldLp_norm_le_other _ (DifferenceProduct.CM.Construction.differenceCoefficient_measurable A hAm m t)
      (DifferenceProduct.CM.Construction.differenceCoefficient_bound A hCm m t)
      (Filter.Eventually.of_forall (fun x => DifferenceProduct.CM.Construction.differenceCoefficient_lipschitz_bound A hA m x t)) q

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferenceBounds.CM.Construction
