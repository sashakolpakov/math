import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EllipticRegularity
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongCutoffGradient
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.WeakEquationLocalization

/-! # Higher Cutoff Regularity -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HigherCutoffRegularity.CM.Construction

noncomputable section

/-! Higher regularity of both genuine forcing terms produced by localization.
An H(n+1) function satisfying the weak equation gains one localized order. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap ContDiff

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

theorem metricCutoffScalarForcing_strongSobolev (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (c : EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport (fun x => A x - c))
    {L : NNReal} (hL : LipschitzWith L A) {C : ℝ} (hC : ∀ x, ‖A x‖ ≤ C)
    (g : 𝓢(E, ℂ)) (u f : Lp ℂ 2 (volume : Measure E))
    (hu : MemSobolev ((n : ℝ) + 1) 2
      (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, ℂ)))
    (hf : MemSobolev (n : ℝ) 2 (f : 𝓢'(E, ℂ))) :
    StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n (WeakEquationLocalization.CM.Construction.metricCutoffScalarForcing b A
      hA.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hC) g u f) := by
  have hS := StrongCutoffOperators.CM.Construction.strongSobolev_schwartz_multiply_adjoint b n g f
    ((StrongSobolev.CM.Construction.strongSobolev_iff_memSobolev b n f).mpr hf)
  have hD := EllipticRegularity.CM.Construction.strongSobolev_gradient_of_memSobolev b n u hu
  have hM := StrongCoefficientProducts.CM.Construction.strongSobolev_coefficient_product b n A c hA hc hL hC (EuclideanGradient.CM.Construction.sobolevVectorGradient b u) hD
  have hK := StrongCutoffGradient.CM.Construction.strongSobolev_cutoffGradient_adjoint b n g _ hM
  simpa only [WeakEquationLocalization.CM.Construction.metricCutoffScalarForcing, sub_eq_add_neg] using hS.add b n (hK.neg b n)

theorem metricCutoffFlux_strongSobolev (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (c : EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport (fun x => A x - c))
    {L : NNReal} (hL : LipschitzWith L A) {C : ℝ} (hC : ∀ x, ‖A x‖ ≤ C)
    (g : 𝓢(E, ℂ)) (u : Lp ℂ 2 (volume : Measure E))
    (hu : MemSobolev ((n : ℝ) + 1) 2
      (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, ℂ))) :
    StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b (n + 1)
      (LpCoefficients.CM.Construction.boundedFieldLp A hA.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hC)
        (CutoffDifferential.CM.Construction.cutoffGradientMultiply b g (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u))) := by
  have hu' : StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b (n + 1)
      (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u) := by
    apply (StrongSobolev.CM.Construction.strongSobolev_iff_memSobolev b (n + 1) _).mpr
    simpa only [Nat.cast_succ] using hu
  exact StrongCoefficientProducts.CM.Construction.strongSobolev_coefficient_product b (n + 1) A c hA hc hL hC _
    (StrongCutoffGradient.CM.Construction.strongSobolev_cutoffGradient b (n + 1) g _ hu')

/-- The actual local weak equation and one previously established Sobolev
order give the next order after cutoff, for every natural n. -/
theorem local_elliptic_cutoff_regularity (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (c : EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport (fun x => A x - c))
    {L : NNReal} (hL : LipschitzWith L A) {C a : ℝ}
    (hC : ∀ x, ‖A x‖ ≤ C) (ha : 0 < a)
    (hpos : ∀ x, ∀ w : EuclideanSpace ℂ ι, a * ‖w‖ * ‖w‖ ≤ inner ℝ (A x w) w)
    (g : 𝓢(E, ℂ)) (hg : ∀ x, g x = Complex.ofReal (g x).re)
    (u f : Lp ℂ 2 (volume : Measure E))
    (hsol : ∀ v : Lp ℂ 2 (volume : Measure E),
      (∫ x, inner ℝ (A x (EuclideanGradient.CM.Construction.sobolevVectorGradient b u x))
        (EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g v) x)) =
        inner ℝ f (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g v)))
    (hu : MemSobolev ((n : ℝ) + 1) 2
      (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, ℂ)))
    (hf : MemSobolev (n : ℝ) 2 (f : 𝓢'(E, ℂ))) :
    MemSobolev ((n : ℝ) + 2) 2 (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)
      (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g u) : 𝓢'(E, ℂ)) := by
  apply EllipticRegularity.CM.Construction.euclidean_elliptic_flux_regularity b n A c hA hc hL hC ha hpos
    (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g u) _ _
    (WeakEquationLocalization.CM.Construction.weak_metric_cutoff_equation b A hA.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hC) g hg u f hsol)
  · exact metricCutoffScalarForcing_strongSobolev b n A c hA hc hL hC g u f hu hf
  · exact metricCutoffFlux_strongSobolev b n A c hA hc hL hC g u hu

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HigherCutoffRegularity.CM.Construction
