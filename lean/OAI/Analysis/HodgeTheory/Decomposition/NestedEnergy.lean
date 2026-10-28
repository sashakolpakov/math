import OAI.Analysis.HodgeTheory.Decomposition.LocalEnergy
import OAI.Analysis.HodgeTheory.Decomposition.VectorNestedCutoffs
import OAI.Analysis.HodgeTheory.Decomposition.PairLocality
import OAI.Analysis.HodgeTheory.Decomposition.SchwartzGradientSupport

/-! # Nested Energy -/

namespace OAI.Analysis.HodgeTheory.Decomposition.NestedEnergy.Constructions

noncomputable section

/-! An outer cutoff equal to one near a chart test leaves the entire
actual local Hodge energy unchanged, including all lower-order terms. -/

open _root_.MeasureTheory
open scoped SchwartzMap ContDiff _root_.Topology

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (η : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η)
  (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
  (A : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → GradientCoefficient.Constructions.ProjectiveGradientValues V n →L[ℝ] GradientCoefficient.Constructions.ProjectiveGradientValues V n)
  (hAm : AEStronglyMeasurable A volume) {C : ℝ} (hAB : ∀ᵐ x ∂volume, ‖A x‖ ≤ C)

theorem projectiveLocalHodgeEnergy_nested
    (ψ : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ))
    (q : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)))
    (hψ : ∀ x ∈ tsupport q, (ψ : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ) =ᶠ[𝓝 x] 1)
    (u : Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) :
    LocalEnergy.Constructions.projectiveLocalHodgeEnergy V e n he η hη hηc hηU A hAm hAB
      (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 ψ u) (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 q) =
    LocalEnergy.Constructions.projectiveLocalHodgeEnergy V e n he η hη hηc hηU A hAm hAB u (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 q) := by
  let b := stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
  let D := VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) b
  let J := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (E := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (by norm_num : (0 : ℝ) ≤ 1)
  let w := VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 ψ u
  let v := VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 q
  have hD := VectorNestedCutoffs.Constructions.vectorSobolevGradient_cutoff_eq_on b ψ hψ u
  have hJ := PairLocality.Constructions.vectorSobolevL2Embedding_cutoff_eq_on ψ (fun x hx => (hψ x hx).eq_of_nhds) u
  have hvD := SchwartzGradientSupport.Constructions.vectorSobolevGradient_schwartz_zero_off_support b q
  have hvJ := PairLocality.Constructions.schwartz_toLp_zero_off_support q
  have hJv : J v = q.toLp 2 volume := VectorEmbeddingRange.Constructions.vectorSobolevL2Embedding_schwartz (by norm_num : (0 : ℝ) ≤ 1) q
  have hP : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy A hAm hAB (D w) (D v) = AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy A hAm hAB (D u) (D v) :=
    PairLocality.Constructions.lp_field_pair_eq_of_local_eq (fun x a => A x a) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpCoefficients.CM.Construction.boundedFieldLp A hAm hAB) (D w) (D u) (D v)
      (tsupport q) (fun a => AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpCoefficients.CM.Construction.boundedFieldLp_coe A hAm hAB a) hD hvD
  have hF : inner ℝ (ProjectiveFluxSobolev.Constructions.projectiveHodgeFluxCutoffL2 V e n he η hη hηc hηU (J w)) (D v) =
      inner ℝ (ProjectiveFluxSobolev.Constructions.projectiveHodgeFluxCutoffL2 V e n he η hη hηc hηU (J u)) (D v) :=
    PairLocality.Constructions.lp_field_pair_eq_of_local_eq (fun x a => η x • GradientCoefficient.Constructions.projectiveHodgeFluxCoefficient V e n x a)
      (ProjectiveFluxSobolev.Constructions.projectiveHodgeFluxCutoffL2 V e n he η hη hηc hηU) (J w) (J u) (D v) (tsupport q)
      (ProjectiveFluxSobolev.Constructions.projectiveHodgeFluxCutoffL2_coe V e n he η hη hηc hηU) hJ hvD
  have hC : inner ℝ (ProjectiveLower.Constructions.projectiveHodgeValueGradientCutoffL2 V e n he η hη hηc hηU (D w)) (J v) =
      inner ℝ (ProjectiveLower.Constructions.projectiveHodgeValueGradientCutoffL2 V e n he η hη hηc hηU (D u)) (J v) := by
    rw [hJv]
    exact PairLocality.Constructions.lp_field_pair_eq_of_local_eq (fun x a => η x • CoefficientHodge.Constructions.projectiveHodgeValueGradientCoefficient V e n x a)
      (ProjectiveLower.Constructions.projectiveHodgeValueGradientCutoffL2 V e n he η hη hηc hηU) (D w) (D u) (q.toLp 2 volume) (tsupport q)
      (ProjectiveLower.Constructions.projectiveHodgeValueGradientCutoffL2_coe V e n he η hη hηc hηU) hD hvJ
  have hE : inner ℝ (ProjectiveLower.Constructions.projectiveHodgeValueValueCutoffL2 V e n he η hη hηc hηU (J w)) (J v) =
      inner ℝ (ProjectiveLower.Constructions.projectiveHodgeValueValueCutoffL2 V e n he η hη hηc hηU (J u)) (J v) := by
    rw [hJv]
    exact PairLocality.Constructions.lp_field_pair_eq_of_local_eq (fun x a => η x • CoefficientHodge.Constructions.projectiveHodgeValueValueCoefficient V e n x a)
      (ProjectiveLower.Constructions.projectiveHodgeValueValueCutoffL2 V e n he η hη hηc hηU) (J w) (J u) (q.toLp 2 volume) (tsupport q)
      (ProjectiveLower.Constructions.projectiveHodgeValueValueCutoffL2_coe V e n he η hη hηc hηU) hJ hvJ
  exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) hP hF) hC) hE

end

end OAI.Analysis.HodgeTheory.Decomposition.NestedEnergy.Constructions
