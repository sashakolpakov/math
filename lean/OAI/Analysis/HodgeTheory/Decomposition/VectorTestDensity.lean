import OAI.Analysis.HodgeTheory.Decomposition.VectorLocalElliptic
import OAI.Analysis.HodgeTheory.Decomposition.VectorSobolevDensity
import OAI.Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful
import OAI.Analysis.HodgeTheory.Decomposition.CompatibleRealInner

/-! # Vector Test Density -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorTestDensity.Constructions

noncomputable section

/-! Compact Schwartz tests determine the full localized vector H¹ weak
equation, including its lower-order flux forcing. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem vectorSobolevDistributionCLM_schwartz (s : ℝ) (f : 𝓢(E, F)) :
    VectorCutoffOperator.Constructions.vectorSobolevDistributionCLM s (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate s f) = (f : 𝓢'(E, F)) := by
  change besselPotential E F (-s)
    (((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Bounds.CM.Construction.sobolevCoordinateEquiv E F s).symm ⟨(f : 𝓢'(E, F)), f.memSobolev⟩) : 𝓢'(E, F)) = _
  rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Bounds.CM.Construction.sobolevCoordinateEquiv_symm_distribution, besselPotential_besselPotential_apply,
    add_neg_cancel, besselPotential_zero, ContinuousLinearMap.id_apply]

theorem vectorSobolevCutoffCLM_schwartz (n : ℕ) (g : 𝓢(E, ℂ)) (f : 𝓢(E, F)) :
    VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM n g (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate (n : ℝ) f) =
      VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate (n : ℝ) (SchwartzMap.smulLeftCLM F g f) := by
  apply VectorCutoffOperator.Constructions.vectorSobolevDistributionCLM_injective (n : ℝ)
  rw [VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM_distribution, vectorSobolevDistributionCLM_schwartz,
    vectorSobolevDistributionCLM_schwartz]
  ext φ
  simp only [smulLeftCLM_apply_apply, SchwartzMap.toTemperedDistributionCLM_apply_apply]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    simp only [SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth,
      smul_smul, smul_eq_mul, mul_comm])

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem vector_local_flux_of_schwartz_tests (b : OrthonormalBasis ι ℝ E)
    (A : E → PiLp 2 (fun _ : ι => EuclideanSpace ℂ κ) →L[ℝ] PiLp 2 (fun _ : ι => EuclideanSpace ℂ κ))
    (hAm : AEStronglyMeasurable A volume) {B : ℝ} (hAB : ∀ᵐ x ∂volume, ‖A x‖ ≤ B)
    (U : Set E) (u f : Lp (EuclideanSpace ℂ κ) 2 (volume : Measure E))
    (h : Lp (PiLp 2 (fun _ : ι => EuclideanSpace ℂ κ)) 2 (volume : Measure E))
    (hsol : ∀ q : 𝓢(E, EuclideanSpace ℂ κ), HasCompactSupport q → tsupport q ⊆ U →
      (∫ x, inner ℝ (A x (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b u x))
        (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 q) x)) =
        inner ℝ f (q.toLp 2 volume) +
          inner ℝ h (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 q)))
    (g : 𝓢(E, ℂ)) (hgc : HasCompactSupport g) (hgU : tsupport g ⊆ U)
    (v : Lp (EuclideanSpace ℂ κ) 2 (volume : Measure E)) :
    (∫ x, inner ℝ (A x (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b u x))
      (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g v) x)) =
      inner ℝ f (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g v)) +
        inner ℝ h (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g v)) := by
  have hclosed : IsClosed {v : Lp (EuclideanSpace ℂ κ) 2 (volume : Measure E) |
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy A hAm hAB (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b u)
        (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g v)) =
      inner ℝ f (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g v)) +
        inner ℝ h (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g v))} := by
    apply isClosed_eq
    · exact ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy A hAm hAB (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b u)).continuous.comp
        ((VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b).continuous.comp (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g).continuous))
    · apply Continuous.add
      · simp_rw [CompatibleRealInner.Constructions.compatible_real_inner]
        exact Complex.continuous_re.comp (continuous_const.inner (𝕜 := ℂ)
          ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (F := EuclideanSpace ℂ κ) (by norm_num : (0 : ℝ) ≤ 1)).continuous.comp
            (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g).continuous))
      · simp_rw [CompatibleRealInner.Constructions.compatible_real_inner]
        exact Complex.continuous_re.comp (continuous_const.inner (𝕜 := ℂ)
          ((VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b).continuous.comp (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g).continuous))
  rw [← AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_apply A hAm hAB]
  exact (VectorSobolevDensity.Constructions.vectorSchwartzSobolevCoordinate_denseRange (E := E) (F := EuclideanSpace ℂ κ) 1).induction_on v
    hclosed (fun φ => by
      change AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy A hAm hAB (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b u)
        (VectorGradient.Constructions.vectorSobolevGradient (F := EuclideanSpace ℂ κ) b (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 φ))) = _
      have hcut := vectorSobolevCutoffCLM_schwartz 1 g φ
      norm_num only [Nat.cast_one] at hcut
      rw [hcut, VectorEmbeddingRange.Constructions.vectorSobolevL2Embedding_schwartz, AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_apply]
      exact hsol _ (ChartCoefficientFaithful.Constructions.schwartz_cutoff_compact g hgc φ) ((ChartCoefficientFaithful.Constructions.schwartz_cutoff_tsupport g φ).trans hgU))

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorTestDensity.Constructions
