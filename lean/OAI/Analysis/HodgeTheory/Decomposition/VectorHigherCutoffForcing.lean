import OAI.Analysis.HodgeTheory.Decomposition.VectorEllipticRegularity
import OAI.Analysis.HodgeTheory.Decomposition.VectorStrongCutoffGradient

/-! # Vector Higher Cutoff Forcing -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorHigherCutoffForcing.Constructions

noncomputable section

section

/-! Higher Sobolev regularity of both actual forcing terms produced by
localizing a vector weak equation with its original flux forcing. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap ContDiff

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [InnerProductSpace ℝ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

theorem vectorCutoffForcing_strongSobolev (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    (A : E → PiLp 2 (fun _ : ι => F) →L[ℝ] PiLp 2 (fun _ : ι => F))
    (c : PiLp 2 (fun _ : ι => F) →L[ℝ] PiLp 2 (fun _ : ι => F))
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport (fun x => A x - c))
    {L : NNReal} (hL : LipschitzWith L A) {C : ℝ} (hC : ∀ x, ‖A x‖ ≤ C)
    (g : 𝓢(E, ℂ)) (u f : Lp F 2 (volume : Measure E))
    (h : Lp (PiLp 2 (fun _ : ι => F)) 2 (volume : Measure E))
    (hu : MemSobolev ((n : ℝ) + 1) 2
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, F)))
    (hf : MemSobolev (n : ℝ) 2 (f : 𝓢'(E, F)))
    (hh : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n h) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n (VectorWeakCutoff.Constructions.vectorCutoffForcing b A
      hA.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hC) g u f h) := by
  have hS := VectorStrongCutoff.Constructions.vectorStrongSobolev_schwartz_multiply_adjoint b n g f
    ((VectorStrongSobolev.Constructions.vectorStrongSobolev_iff_memSobolev b n f).mpr hf)
  have hD := VectorStrongGradient.Constructions.vectorStrongSobolev_gradient_of_memSobolev b n u hu
  have hM := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongCoefficientProducts.CM.Construction.strongSobolev_coefficient_product b n A c hA hc hL hC (VectorGradient.Constructions.vectorSobolevGradient (F := F) b u) hD
  have hK := VectorStrongCutoffGradient.Constructions.vectorStrongSobolev_cutoffGradient_adjoint b n g _ hM
  have hKh := VectorStrongCutoffGradient.Constructions.vectorStrongSobolev_cutoffGradient_adjoint b n g h hh
  simpa only [VectorWeakCutoff.Constructions.vectorCutoffForcing, sub_eq_add_neg] using (hS.add b n hKh).add b n (hK.neg b n)

theorem vectorCutoffFlux_strongSobolev (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    (A : E → PiLp 2 (fun _ : ι => F) →L[ℝ] PiLp 2 (fun _ : ι => F))
    (c : PiLp 2 (fun _ : ι => F) →L[ℝ] PiLp 2 (fun _ : ι => F))
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport (fun x => A x - c))
    {L : NNReal} (hL : LipschitzWith L A) {C : ℝ} (hC : ∀ x, ‖A x‖ ≤ C)
    (g : 𝓢(E, ℂ)) (u : Lp F 2 (volume : Measure E))
    (h : Lp (PiLp 2 (fun _ : ι => F)) 2 (volume : Measure E))
    (hu : MemSobolev ((n : ℝ) + 1) 2
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, F)))
    (hh : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b (n + 1) h) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b (n + 1)
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g h +
        AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpCoefficients.CM.Construction.boundedFieldLp A hA.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hC)
          (VectorCutoffGradient.Constructions.vectorCutoffGradientMultiply (F := F) b g (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u))) := by
  have hu' : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b (n + 1)
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u) := by
    apply (VectorStrongSobolev.Constructions.vectorStrongSobolev_iff_memSobolev b (n + 1) _).mpr
    simpa only [Nat.cast_succ] using hu
  exact (VectorStrongCutoff.Constructions.vectorStrongSobolev_schwartz_multiply b (n + 1) g h hh).add b (n + 1)
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongCoefficientProducts.CM.Construction.strongSobolev_coefficient_product b (n + 1) A c hA hc hL hC _
      (VectorStrongCutoffGradient.Constructions.vectorStrongSobolev_cutoffGradient b (n + 1) g _ hu'))

end

/-! A genuine local vector weak flux equation gains one further Sobolev
order after cutoff, with integrated rather than pointwise coercivity. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap ContDiff

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [InnerProductSpace ℝ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

theorem vector_local_elliptic_flux_regularity (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    (A : E → PiLp 2 (fun _ : ι => F) →L[ℝ] PiLp 2 (fun _ : ι => F))
    (c : PiLp 2 (fun _ : ι => F) →L[ℝ] PiLp 2 (fun _ : ι => F))
    (hA : ContDiff ℝ ∞ A) (hc : HasCompactSupport (fun x => A x - c))
    {L : NNReal} (hL : LipschitzWith L A) {C a β : ℝ}
    (hC : ∀ x, ‖A x‖ ≤ C) (ha : 0 < a) (hβ : 0 ≤ β)
    (hgard : ∀ y : E, ∀ v : Lp F 2 (volume : Measure E),
      a * ‖VectorGradient.Constructions.vectorSobolevGradient (F := F) b v‖ * ‖VectorGradient.Constructions.vectorSobolevGradient (F := F) b v‖ ≤
        (∫ x, inner ℝ (A (x + y) (VectorGradient.Constructions.vectorSobolevGradient (F := F) b v x)) (VectorGradient.Constructions.vectorSobolevGradient (F := F) b v x)) +
          β * ‖AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) v‖ ^ 2)
    (g : 𝓢(E, ℂ)) (hg : ∀ x, g x = Complex.ofReal (g x).re)
    (u f : Lp F 2 (volume : Measure E)) (h : Lp (PiLp 2 (fun _ : ι => F)) 2 (volume : Measure E))
    (hsol : ∀ v : Lp F 2 (volume : Measure E),
      (∫ x, inner ℝ (A x (VectorGradient.Constructions.vectorSobolevGradient (F := F) b u x))
        (VectorGradient.Constructions.vectorSobolevGradient (F := F) b (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g v) x)) =
        inner ℝ f (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g v)) +
        inner ℝ h (VectorGradient.Constructions.vectorSobolevGradient (F := F) b (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g v)))
    (hu : MemSobolev ((n : ℝ) + 1) 2
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u : 𝓢'(E, F)))
    (hf : MemSobolev (n : ℝ) 2 (f : 𝓢'(E, F)))
    (hh : MemSobolev ((n : ℝ) + 1) 2 (h : 𝓢'(E, PiLp 2 (fun _ : ι => F)))) :
    MemSobolev ((n : ℝ) + 2) 2
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g u) : 𝓢'(E, F)) := by
  have hh' : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b (n + 1) h := by
    apply (VectorStrongSobolev.Constructions.vectorStrongSobolev_iff_memSobolev b (n + 1) h).mpr
    simpa only [Nat.cast_succ] using hh
  apply VectorEllipticRegularity.Constructions.vector_elliptic_flux_regularity b n A c hA hc hL hC ha hβ hgard
    (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g u) _ _
    (VectorWeakCutoff.Constructions.vector_weak_cutoff_flux b A hA.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hC) g hg u f h hsol)
  · exact vectorCutoffForcing_strongSobolev b n A c hA hc hL hC g u f h hu hf hh'.1
  · exact vectorCutoffFlux_strongSobolev b n A c hA hc hL hC g u h hu hh'

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorHigherCutoffForcing.Constructions
