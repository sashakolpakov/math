import OAI.Analysis.HodgeTheory.Decomposition.VectorCutoffGradient
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EllipticDifferenceEstimate

/-! # Vector Cutoff Difference Bounds -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorCutoffDifferenceBounds.Constructions

noncomputable section

/-! The flux created by a smooth cutoff has bounded spatial difference
quotients, including after application of Lipschitz metric coefficients. -/

open _root_.MeasureTheory
open scoped SchwartzMap LineDeriv

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EllipticDifferenceEstimate.CM.Construction

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [InnerProductSpace ℝ F] [IsScalarTower ℝ ℂ F]

omit [CompleteSpace F] in
theorem realL2Difference_finiteSynthesis (m : E) (t : ℝ)
    (u v : PiLp 2 (fun _ : ι => Lp F 2 (volume : Measure E)))
    (h : ∀ i, v i = VectorDifferences.Constructions.vectorL2DifferenceQuotient m t (u i)) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference m t (FiniteLp.Constructions.finiteLpSynthesis (𝕜 := ℂ) (F := F) (ι := ι) (μ := (volume : Measure E)) u) =
      FiniteLp.Constructions.finiteLpSynthesis (𝕜 := ℂ) (F := F) (ι := ι) (μ := (volume : Measure E)) v := by
  have hc : ∀ᵐ x ∂(volume : Measure E), ∀ i,
      (v i) x = (t : ℂ)⁻¹ • ((u i) (x + t • m) - (u i) x) := by
    apply ae_all_iff.mpr
    intro i
    rw [h i]
    exact VectorDifferences.Constructions.vectorL2DifferenceQuotient_coe m t (u i)
  apply Lp.ext
  filter_upwards [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference_coe m t (FiniteLp.Constructions.finiteLpSynthesis (𝕜 := ℂ) (F := F) (ι := ι) (μ := (volume : Measure E)) u),
    FiniteLp.Constructions.finiteLpSynthesis_coe (𝕜 := ℂ) u,
    (measurePreserving_add_right volume (t • m)).quasiMeasurePreserving.ae
      (FiniteLp.Constructions.finiteLpSynthesis_coe (𝕜 := ℂ) u),
    FiniteLp.Constructions.finiteLpSynthesis_coe (𝕜 := ℂ) v, hc]
    with x hd h0 ht hv hx
  rw [hd, h0, ht, hv]
  apply PiLp.ext
  intro i
  change t⁻¹ • (u i (x + t • m) - u i x) = v i x
  rw [hx i, ← Complex.ofReal_inv]
  exact (IsScalarTower.algebraMap_smul ℂ t⁻¹ _).symm

omit [CompleteSpace F] in
theorem vectorSynthesis_difference_bounded (m : E)
    (u : PiLp 2 (fun _ : ι => Lp F 2 (volume : Measure E)))
    (h : ∀ i, ∃ B : ℝ, ∀ t, ‖VectorDifferences.Constructions.vectorL2DifferenceQuotient m t (u i)‖ ≤ B) :
    ∃ B : ℝ, ∀ t, ‖AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference m t
      (FiniteLp.Constructions.finiteLpSynthesis (𝕜 := ℂ) (F := F) (ι := ι) (μ := (volume : Measure E)) u)‖ ≤ B := by
  classical
  choose B hB using h
  let C : ℝ := ∑ i, max (B i) 0
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => le_max_right _ _)
  let T := (PiLp.continuousLinearEquiv 2 ℂ
    (fun _ : ι => Lp F 2 (volume : Measure E))).symm.toContinuousLinearMap
  refine ⟨‖T‖ * C, fun t => ?_⟩
  let v := T (fun i => VectorDifferences.Constructions.vectorL2DifferenceQuotient m t (u i))
  rw [realL2Difference_finiteSynthesis m t u v (fun _ => rfl)]
  have hs : ‖FiniteLp.Constructions.finiteLpSynthesis (𝕜 := ℂ) (F := F) (ι := ι) (μ := (volume : Measure E)) v‖ = ‖v‖ :=
    FiniteLp.Constructions.finiteLpSynthesis_norm (𝕜 := ℂ) v
  rw [hs]
  apply (T.le_opNorm _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg T)
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro i
  exact (hB i t).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun j _ => le_max_right (B j) 0) (Finset.mem_univ i)))

theorem vectorCutoffGradient_difference_bounded (b : OrthonormalBasis ι ℝ E)
    (g : 𝓢(E, ℂ)) (u : Lp F 2 (volume : Measure E)) (m : E) :
    ∃ B : ℝ, ∀ t, ‖AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference m t (VectorCutoffGradient.Constructions.vectorCutoffGradientMultiply (F := F) b g
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u))‖ ≤ B := by
  apply vectorSynthesis_difference_bounded m
  intro i
  refine ⟨‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ *
    ((2 * Real.pi * ‖m‖) * ‖VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 (∂_{b i} g : 𝓢(E, ℂ)) u‖), fun t => ?_⟩
  change ‖VectorDifferences.Constructions.vectorL2DifferenceQuotient m t ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply (∂_{b i} g : 𝓢(E, ℂ))
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u))‖ ≤ _
  rw [map_smul, norm_smul,
    ← VectorCutoffDifferential.Constructions.vectorSobolevCutoffCLM_embedding]
  exact mul_le_mul_of_nonneg_left (VectorDifferenceBounds.Constructions.vectorL2DifferenceQuotient_sobolev_bound m t _)
    (norm_nonneg _)

omit [InnerProductSpace ℂ F] [CompleteSpace F] [IsScalarTower ℝ ℂ F] in
theorem vectorBoundedField_difference_bounded
    (A : E → PiLp 2 (fun _ : ι => F) →L[ℝ] PiLp 2 (fun _ : ι => F)) {L : NNReal}
    (hA : LipschitzWith L A) {C : ℝ} (hC : ∀ x, ‖A x‖ ≤ C)
    (q : Lp (PiLp 2 (fun _ : ι => F)) 2 (volume : Measure E)) (m : E)
    (hq : ∃ B : ℝ, ∀ t, ‖AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference m t q‖ ≤ B) :
    ∃ B : ℝ, ∀ t, ‖AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference m t (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpCoefficients.CM.Construction.boundedFieldLp A hA.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hC) q)‖ ≤ B := by
  obtain ⟨B, hB⟩ := hq
  have hC₀ : 0 ≤ C := (norm_nonneg (A 0)).trans (hC 0)
  let hAm := hA.continuous.aestronglyMeasurable (μ := (volume : Measure E))
  let hCm : ∀ᵐ x ∂(volume : Measure E), ‖A x‖ ≤ C := Filter.Eventually.of_forall hC
  refine ⟨C * B + ((L : ℝ) * ‖m‖) * ‖q‖, fun t => ?_⟩
  rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference_coefficient_product]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EllipticDifferenceEstimate.CM.Construction.boundedFieldLp_norm_le_other _ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.translatedCoefficient_measurable A hAm (t • m))
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.translatedCoefficient_bound A hCm (t • m)) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.translatedCoefficient_bound A hCm (t • m))
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference m t q)).trans (mul_le_mul_of_nonneg_left (hB t) hC₀)
  · exact AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EllipticDifferenceEstimate.CM.Construction.boundedFieldLp_norm_le_other _ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.differenceCoefficient_measurable A hAm m t)
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.differenceCoefficient_bound A hCm m t)
      (Filter.Eventually.of_forall (fun x => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.differenceCoefficient_lipschitz_bound A hA m x t)) q

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorCutoffDifferenceBounds.Constructions
