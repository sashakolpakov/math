import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.WeakEquationLocalization
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferenceBounds
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GradientSupport

/-! # Local Elliptic -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalElliptic.CM.Construction

noncomputable section

/-! Interior H2 regularity for a genuine weak Dirichlet solution. The
coefficients need only agree with a positive Lipschitz extension near the
support of the cutoff. -/

open _root_.MeasureTheory TemperedDistribution Set
open scoped SchwartzMap

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

theorem local_elliptic_cutoff_h2 (b : OrthonormalBasis ι ℝ E)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι) {L : NNReal}
    (hA : LipschitzWith L A) {C a : ℝ} (hC : ∀ x, ‖A x‖ ≤ C) (ha : 0 < a)
    (hpos : ∀ x, ∀ w : EuclideanSpace ℂ ι, a * ‖w‖ * ‖w‖ ≤ inner ℝ (A x w) w)
    (g : 𝓢(E, ℂ)) (hg : ∀ x, g x = Complex.ofReal (g x).re)
    (u f : Lp ℂ 2 (volume : Measure E))
    (hsol : ∀ v : Lp ℂ 2 (volume : Measure E),
      (∫ x, inner ℝ (A x (EuclideanGradient.CM.Construction.sobolevVectorGradient b u x))
        (EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g v) x)) =
        inner ℝ f (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g v))) :
    MemSobolev 2 2 ((SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)
      (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g u) : Lp ℂ 2 volume) : 𝓢'(E, ℂ)) := by
  obtain ⟨f₀, hf₀⟩ := WeakEquationLocalization.CM.Construction.weak_metric_cutoff_flux b A hA.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall hC) g hg u f hsol
  apply Elliptic.CM.Construction.euclidean_elliptic_flux_h2_regularity b A hA hC ha hpos _ f₀ _ hf₀
  intro i
  exact CutoffDifferenceBounds.CM.Construction.boundedField_difference_bounded A hA hC _ (b i)
    (CutoffDifferenceBounds.CM.Construction.cutoffGradient_difference_bounded b g u (b i))

theorem cutoff_energy_coefficient_eq (b : OrthonormalBasis ι ℝ E)
    (A B : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (g : 𝓢(E, ℂ)) (hAB : ∀ x ∈ tsupport g, A x = B x)
    (u v : Lp ℂ 2 (volume : Measure E)) :
    (∫ x, inner ℝ (A x (EuclideanGradient.CM.Construction.sobolevVectorGradient b u x))
      (EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g v) x)) =
    (∫ x, inner ℝ (B x (EuclideanGradient.CM.Construction.sobolevVectorGradient b u x))
      (EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g v) x)) := by
  let w : SobolevIs.CM.Construction.supportedH1Coordinates (tsupport g) :=
    ⟨SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g v, SobolevSmoothDensity.CM.Construction.sobolevCutoffCLM_mem_supported g (subset_tsupport g) v⟩
  have hw : ∀ᵐ x ∂(volume : Measure E), x ∉ tsupport g →
      EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g v) x = 0 :=
    GradientSupport.CM.Construction.supportedH1VectorGradient_support b isClosed_closure w
  apply integral_congr_ae
  filter_upwards [hw] with x hx
  by_cases h : x ∈ tsupport g
  · rw [hAB x h]
  · rw [hx h, inner_zero_right, inner_zero_right]

/-- A weak solution on the completed supported H1 domain has genuine H2
regularity after any interior cutoff where a uniformly elliptic Lipschitz
extension of the coefficients is available. -/
theorem supported_weak_solution_interior_h2 (b : OrthonormalBasis ι ℝ E)
    (A B : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι) {L : NNReal}
    (hA : LipschitzWith L A) {C a : ℝ} (hC : ∀ x, ‖A x‖ ≤ C) (ha : 0 < a)
    (hpos : ∀ x, ∀ w : EuclideanSpace ℂ ι, a * ‖w‖ * ‖w‖ ≤ inner ℝ (A x w) w)
    {K : Set E} (g : 𝓢(E, ℂ)) (hg : ∀ x, g x = Complex.ofReal (g x).re)
    (hgK : Function.support (g : E → ℂ) ⊆ K) (hAB : ∀ x ∈ tsupport g, A x = B x)
    (u : SobolevIs.CM.Construction.supportedH1Coordinates K) (f : Lp ℂ 2 (volume : Measure E))
    (hsol : ∀ v : SobolevIs.CM.Construction.supportedH1Coordinates K,
      (∫ x, inner ℝ (B x (GradientSupport.CM.Construction.supportedH1VectorGradient b K u x))
        (GradientSupport.CM.Construction.supportedH1VectorGradient b K v x)) = inner ℝ f (SobolevIs.CM.Construction.supportedH1Embedding K v)) :
    MemSobolev 2 2 ((SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)
      (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g u.val) : Lp ℂ 2 volume) : 𝓢'(E, ℂ)) := by
  apply local_elliptic_cutoff_h2 b A hA hC ha hpos g hg u.val f
  intro v
  rw [cutoff_energy_coefficient_eq b A B g hAB]
  exact hsol ⟨SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g v, SobolevSmoothDensity.CM.Construction.sobolevCutoffCLM_mem_supported g hgK v⟩

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalElliptic.CM.Construction
