import OAI.Analysis.HodgeTheory.Decomposition.FrozenEstimate
import OAI.Analysis.HodgeTheory.Decomposition.GradientEnergy

/-! # Frozen Gradient -/

namespace OAI.Analysis.HodgeTheory.Decomposition.FrozenGradient.Constructions

noncomputable section

/-! An unweighted gradient estimate for the actual frozen Hodge operators. -/

open _root_.MeasureTheory LineDeriv
open scoped SchwartzMap BigOperators

section Integral

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem schwartz_weighted_energy_le (A : F →L[ℂ] F) (f : 𝓢(E, F)) :
    (∫ x, (inner ℂ (A (f x)) (f x)).re) ≤ ‖A‖ * ∫ x, ‖f x‖ ^ 2 := by
  rw [← integral_const_mul]
  have hi : Integrable (fun x => (inner ℂ (A (f x)) (f x)).re) volume :=
    Complex.reCLM.integrable_comp (WeightedPlancherel.Constructions.schwartz_inner_integrable (SchwartzMap.postcompCLM A f) f)
  apply integral_mono hi ((GradientEnergy.Constructions.schwartz_normsq_integrable f).const_mul ‖A‖)
  intro x
  calc
    (inner ℂ (A (f x)) (f x)).re ≤ ‖A (f x)‖ * ‖f x‖ := re_inner_le_norm (𝕜 := ℂ) _ _
    _ ≤ (‖A‖ * ‖f x‖) * ‖f x‖ := mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
    _ = _ := by ring

end Integral

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)

theorem projectiveFrozen_gradient_estimate
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ C : ℝ, 0 < C ∧
      ∀ a : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)),
        (∑ i : AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V,
          ∫ x, ‖∂_{stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) i} a x‖ ^ 2) ≤
            C * ((∫ x, ‖FrozenFourier.Constructions.projectiveFrozenD V (n + 1) a x‖ ^ 2) +
              ∫ x, ‖FrozenFourier.Constructions.projectiveFrozenDelta V e n he z hz a x‖ ^ 2) := by
  obtain ⟨c, hc, hest⟩ := FrozenEstimate.Constructions.projectiveFrozen_firstOrder_estimate V e n he z hz
  let A := PrincipalAdjoint.Constructions.projectiveComplexWeight V e (n + 1 + 1) z
  let B := PrincipalAdjoint.Constructions.projectiveComplexWeight V e n z
  let M := max ‖A‖ ‖B‖ + 1
  have hM : 0 < M := by dsimp [M]; linarith [norm_nonneg A, le_max_left ‖A‖ ‖B‖]
  let k := ‖(2 * Real.pi * Complex.I : ℂ)‖ ^ 2
  have hk : 0 < k := by
    apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  refine ⟨k / c * M, mul_pos (div_pos hk hc) hM, fun a => ?_⟩
  let d := ∫ x, ‖FrozenFourier.Constructions.projectiveFrozenD V (n + 1) a x‖ ^ 2
  let t := ∫ x, ‖FrozenFourier.Constructions.projectiveFrozenDelta V e n he z hz a x‖ ^ 2
  have hd : 0 ≤ d := integral_nonneg (fun _ => sq_nonneg _)
  have ht : 0 ≤ t := integral_nonneg (fun _ => sq_nonneg _)
  have hA : ‖A‖ ≤ M := (le_max_left _ _).trans (by dsimp [M]; linarith)
  have hB : ‖B‖ ≤ M := (le_max_right _ _).trans (by dsimp [M]; linarith)
  have h := (hest a).trans (add_le_add
    (schwartz_weighted_energy_le A (FrozenFourier.Constructions.projectiveFrozenD V (n + 1) a))
    (schwartz_weighted_energy_le B (FrozenFourier.Constructions.projectiveFrozenDelta V e n he z hz a)))
  have hupper : ‖A‖ * d + ‖B‖ * t ≤ M * (d + t) := by
    rw [mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_right hA hd) (mul_le_mul_of_nonneg_right hB ht)
  have hfinal := mul_le_mul_of_nonneg_left (h.trans hupper) (div_pos hk hc).le
  rw [GradientEnergy.Constructions.schwartz_gradient_energy]
  rw [← mul_assoc, div_mul_cancel₀ _ hc.ne'] at hfinal
  exact hfinal.trans_eq (mul_assoc _ _ _).symm

end

end OAI.Analysis.HodgeTheory.Decomposition.FrozenGradient.Constructions
