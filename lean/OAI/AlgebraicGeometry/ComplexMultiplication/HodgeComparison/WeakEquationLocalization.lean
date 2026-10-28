import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Elliptic

/-! # Weak Equation Localization -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.WeakEquationLocalization.CM.Construction

noncomputable section

/-! Localization of the actual weak metric equation. The resulting scalar
forcing is obtained from bounded Hilbert adjoints, and the flux is the actual
coefficient field applied to the cutoff-gradient commutator. -/

open _root_.MeasureTheory
open scoped SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [InnerProductSpace ℝ F]
  [IsScalarTower ℝ ℂ F]

theorem boundedFieldEnergy_real_cutoff (A : E → F →L[ℝ] F)
    (hA : AEStronglyMeasurable A (volume : Measure E))
    {C : ℝ} (hC : ∀ᵐ x ∂(volume : Measure E), ‖A x‖ ≤ C)
    (g : 𝓢(E, ℂ)) (hg : ∀ x, g x = Complex.ofReal (g x).re)
    (u v : Lp F 2 (volume : Measure E)) :
    inner ℝ (LpCoefficients.CM.Construction.boundedFieldLp A hA hC (CutoffDifferential.CM.Construction.schwartzL2Multiply g u)) v =
      inner ℝ (LpCoefficients.CM.Construction.boundedFieldLp A hA hC u) (CutoffDifferential.CM.Construction.schwartzL2Multiply g v) := by
  change CoerciveKernelSolver.CM.Construction.boundedFieldEnergy A hA hC (CutoffDifferential.CM.Construction.schwartzL2Multiply g u) v =
    CoerciveKernelSolver.CM.Construction.boundedFieldEnergy A hA hC u (CutoffDifferential.CM.Construction.schwartzL2Multiply g v)
  rw [CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_apply, CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_apply]
  apply integral_congr_ae
  filter_upwards [CutoffDifferential.CM.Construction.schwartzL2Multiply_coe g u, CutoffDifferential.CM.Construction.schwartzL2Multiply_coe g v] with x hu hv
  have hsmul (r : ℝ) (w : F) : (r : ℂ) • w = r • w := IsScalarTower.algebraMap_smul ℂ r w
  rw [hu, hv, hg x, hsmul, hsmul, map_smul,
    real_inner_smul_left, real_inner_smul_right]

variable {ι : Type*} [Fintype ι]

def metricCutoffScalarForcing (b : OrthonormalBasis ι ℝ E)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (hA : AEStronglyMeasurable A (volume : Measure E))
    {C : ℝ} (hC : ∀ᵐ x ∂(volume : Measure E), ‖A x‖ ≤ C)
    (g : 𝓢(E, ℂ)) (u f : Lp ℂ 2 (volume : Measure E)) : Lp ℂ 2 (volume : Measure E) :=
  ((CutoffDifferential.CM.Construction.schwartzL2Multiply (F := ℂ) g).restrictScalars ℝ).adjoint f -
    ((CutoffDifferential.CM.Construction.cutoffGradientMultiply b g).restrictScalars ℝ).adjoint (LpCoefficients.CM.Construction.boundedFieldLp A hA hC (EuclideanGradient.CM.Construction.sobolevVectorGradient b u))

omit [NormedAddCommGroup F] [InnerProductSpace ℂ F] [InnerProductSpace ℝ F]
  [IsScalarTower ℝ ℂ F] in
theorem weak_metric_cutoff_equation (b : OrthonormalBasis ι ℝ E)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (hA : AEStronglyMeasurable A (volume : Measure E))
    {C : ℝ} (hC : ∀ᵐ x ∂(volume : Measure E), ‖A x‖ ≤ C)
    (g : 𝓢(E, ℂ)) (hg : ∀ x, g x = Complex.ofReal (g x).re)
    (u f : Lp ℂ 2 (volume : Measure E))
    (hsol : ∀ v : Lp ℂ 2 (volume : Measure E),
      (∫ x, inner ℝ (A x (EuclideanGradient.CM.Construction.sobolevVectorGradient b u x))
        (EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g v) x)) =
        inner ℝ f (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g v))) :
      EllipticDifferenceEstimate.CM.Construction.IsEuclideanWeakMetricFluxSolution b A (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g u)
        (metricCutoffScalarForcing b A hA hC g u f)
        (LpCoefficients.CM.Construction.boundedFieldLp A hA hC (CutoffDifferential.CM.Construction.cutoffGradientMultiply b g
          (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u))) := by
  let J := SobolevIs.CM.Construction.sobolevL2Embedding (E := E) (F := ℂ) (by norm_num : (0 : ℝ) ≤ 1)
  let D := EuclideanGradient.CM.Construction.sobolevVectorGradient b
  let M := LpCoefficients.CM.Construction.boundedFieldLp (p := 2) A hA hC
  let S := (CutoffDifferential.CM.Construction.schwartzL2Multiply (F := ℂ) g).restrictScalars ℝ
  let K := (CutoffDifferential.CM.Construction.cutoffGradientMultiply b g).restrictScalars ℝ
  intro v
  have hweak : inner ℝ (M (D u)) (D (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g v)) =
      inner ℝ f (J (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g v)) :=
    (CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_apply A hA hC (D u) (D (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g v))).trans (hsol v)
  dsimp only [D, J] at hweak
  rw [CutoffDifferential.CM.Construction.sobolevVectorGradient_cutoff, CutoffDifferential.CM.Construction.sobolevCutoffCLM_embedding, inner_add_right] at hweak
  rw [← CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_apply A hA hC]
  change inner ℝ (M (D (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g u))) (D v) =
    inner ℝ (S.adjoint f - K.adjoint (M (D u))) (J v) + inner ℝ (M (K (J u))) (D v)
  rw [CutoffDifferential.CM.Construction.sobolevVectorGradient_cutoff, map_add, inner_add_left,
    boundedFieldEnergy_real_cutoff A hA hC g hg,
    inner_sub_left, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left]
  simp only [M, D, J, K, S, ContinuousLinearMap.coe_restrictScalars'] at hweak ⊢
  linarith [hweak]

omit [NormedAddCommGroup F] [InnerProductSpace ℂ F] [InnerProductSpace ℝ F]
  [IsScalarTower ℝ ℂ F] in
theorem weak_metric_cutoff_flux (b : OrthonormalBasis ι ℝ E)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (hA : AEStronglyMeasurable A (volume : Measure E))
    {C : ℝ} (hC : ∀ᵐ x ∂(volume : Measure E), ‖A x‖ ≤ C)
    (g : 𝓢(E, ℂ)) (hg : ∀ x, g x = Complex.ofReal (g x).re)
    (u f : Lp ℂ 2 (volume : Measure E))
    (hsol : ∀ v : Lp ℂ 2 (volume : Measure E),
      (∫ x, inner ℝ (A x (EuclideanGradient.CM.Construction.sobolevVectorGradient b u x))
        (EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g v) x)) =
        inner ℝ f (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g v))) :
    ∃ f₀ : Lp ℂ 2 (volume : Measure E),
      EllipticDifferenceEstimate.CM.Construction.IsEuclideanWeakMetricFluxSolution b A (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g u) f₀
        (LpCoefficients.CM.Construction.boundedFieldLp A hA hC (CutoffDifferential.CM.Construction.cutoffGradientMultiply b g
          (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u))) :=
  ⟨metricCutoffScalarForcing b A hA hC g u f, weak_metric_cutoff_equation b A hA hC g hg u f hsol⟩

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.WeakEquationLocalization.CM.Construction
