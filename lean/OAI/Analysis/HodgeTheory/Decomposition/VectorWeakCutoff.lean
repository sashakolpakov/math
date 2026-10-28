import OAI.Analysis.HodgeTheory.Decomposition.VectorCutoffGradient
import OAI.Analysis.HodgeTheory.Decomposition.VectorElliptic
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.WeakEquationLocalization

/-! # Vector Weak Cutoff -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorWeakCutoff.Constructions

noncomputable section

/-! Localization of a genuine vector weak equation, retaining both its
L² forcing and its first-order flux forcing. -/

open _root_.MeasureTheory
open scoped SchwartzMap
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.WeakEquationLocalization.CM.Construction

theorem adjoint_forcing_pair {H₀ H₁ : Type*}
    [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (S : H₀ →L[ℝ] H₀) (K : H₀ →L[ℝ] H₁) (f v : H₀) (h k : H₁) :
    inner ℝ (S.adjoint f + K.adjoint h - K.adjoint k) v =
      inner ℝ f (S v) + inner ℝ h (K v) - inner ℝ k (K v) := by
  rw [inner_sub_left, inner_add_left,
    ContinuousLinearMap.adjoint_inner_left S v f,
    ContinuousLinearMap.adjoint_inner_left K v h,
    ContinuousLinearMap.adjoint_inner_left K v k]

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [InnerProductSpace ℝ F]
  [IsScalarTower ℝ ℂ F]

theorem vectorRealCutoff_pair (g : 𝓢(E, ℂ)) (hg : ∀ x, g x = Complex.ofReal (g x).re)
    (u v : Lp F 2 (volume : Measure E)) :
    inner ℝ u (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g v) = inner ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g u) v := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply_coe g u, AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply_coe g v] with x hu hv
  have hsmul (r : ℝ) (w : F) : (r : ℂ) • w = r • w := IsScalarTower.algebraMap_smul ℂ r w
  rw [hu, hv, hg x, hsmul, hsmul, real_inner_smul_left, real_inner_smul_right]

variable [CompleteSpace F] [Fintype ι]

def vectorCutoffForcing (b : OrthonormalBasis ι ℝ E)
    (A : E → PiLp 2 (fun _ : ι => F) →L[ℝ] PiLp 2 (fun _ : ι => F))
    (hA : AEStronglyMeasurable A (volume : Measure E))
    {C : ℝ} (hC : ∀ᵐ x ∂(volume : Measure E), ‖A x‖ ≤ C)
    (g : 𝓢(E, ℂ)) (u f : Lp F 2 (volume : Measure E))
    (h : Lp (PiLp 2 (fun _ : ι => F)) 2 (volume : Measure E)) : Lp F 2 (volume : Measure E) :=
  ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply (F := F) g).restrictScalars ℝ).adjoint f +
    ((VectorCutoffGradient.Constructions.vectorCutoffGradientMultiply (F := F) b g).restrictScalars ℝ).adjoint h -
    ((VectorCutoffGradient.Constructions.vectorCutoffGradientMultiply (F := F) b g).restrictScalars ℝ).adjoint
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpCoefficients.CM.Construction.boundedFieldLp A hA hC (VectorGradient.Constructions.vectorSobolevGradient (F := F) b u))

theorem vector_weak_cutoff_flux (b : OrthonormalBasis ι ℝ E)
    (A : E → PiLp 2 (fun _ : ι => F) →L[ℝ] PiLp 2 (fun _ : ι => F))
    (hA : AEStronglyMeasurable A (volume : Measure E))
    {C : ℝ} (hC : ∀ᵐ x ∂(volume : Measure E), ‖A x‖ ≤ C)
    (g : 𝓢(E, ℂ)) (hg : ∀ x, g x = Complex.ofReal (g x).re)
    (u f : Lp F 2 (volume : Measure E))
    (h : Lp (PiLp 2 (fun _ : ι => F)) 2 (volume : Measure E))
    (hsol : ∀ v : Lp F 2 (volume : Measure E),
      (∫ x, inner ℝ (A x (VectorGradient.Constructions.vectorSobolevGradient (F := F) b u x))
        (VectorGradient.Constructions.vectorSobolevGradient (F := F) b (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g v) x)) =
        inner ℝ f (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g v)) +
        inner ℝ h (VectorGradient.Constructions.vectorSobolevGradient (F := F) b (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g v))) :
    VectorEllipticEstimate.Constructions.IsVectorWeakFluxSolution b A (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g u)
      (vectorCutoffForcing b A hA hC g u f h)
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g h + AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpCoefficients.CM.Construction.boundedFieldLp A hA hC (VectorCutoffGradient.Constructions.vectorCutoffGradientMultiply (F := F) b g
        (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u))) := by
  let J := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (E := E) (F := F) (by norm_num : (0 : ℝ) ≤ 1)
  let D := VectorGradient.Constructions.vectorSobolevGradient (F := F) b
  let M := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpCoefficients.CM.Construction.boundedFieldLp (p := 2) A hA hC
  let S := (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply (F := F) g).restrictScalars ℝ
  let K := (VectorCutoffGradient.Constructions.vectorCutoffGradientMultiply (F := F) b g).restrictScalars ℝ
  intro v
  have hweak : inner ℝ (M (D u)) (D (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g v)) =
      inner ℝ f (J (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g v)) + inner ℝ h (D (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g v)) :=
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_apply A hA hC (D u) (D (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g v))).trans (hsol v)
  dsimp only [D, J] at hweak
  rw [VectorCutoffGradient.Constructions.vectorSobolevGradient_cutoff, VectorCutoffDifferential.Constructions.vectorSobolevCutoffCLM_embedding,
    inner_add_right, inner_add_right, vectorRealCutoff_pair g hg h] at hweak
  rw [← AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_apply A hA hC]
  change inner ℝ (M (D (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g u))) (D v) =
    inner ℝ (S.adjoint f + K.adjoint h - K.adjoint (M (D u))) (J v) +
      inner ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g h + M (K (J u))) (D v)
  rw [VectorCutoffGradient.Constructions.vectorSobolevGradient_cutoff, map_add, inner_add_left,
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.WeakEquationLocalization.CM.Construction.boundedFieldEnergy_real_cutoff A hA hC g hg, adjoint_forcing_pair S K f (J v) h (M (D u)),
    inner_add_left]
  simp only [M, D, J, K, S, ContinuousLinearMap.coe_restrictScalars'] at hweak ⊢
  linarith [hweak]

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorWeakCutoff.Constructions
