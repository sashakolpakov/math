import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveBochner.LocalGain
import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveBochner.NestedTest
import OAI.Analysis.HodgeTheory.Decomposition.NestedCutoffNeighborhood

/-! # All Orders -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

section

/-! Nested cutoffs turn regularity of every compact localization into the next Sobolev order for the same native equation. -/

open _root_.TopologicalSpace _root_.MeasureTheory TemperedDistribution
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.NestedCutoffNeighborhood.Constructions

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveBochner_order_step (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (U : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (hU : IsOpen U) (hUD : U ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) (hηone : ∀ x ∈ U, η x = 1)
    (n : ℕ) (A : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1 →L[ℝ] GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (c : GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1 →L[ℝ] GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)
    (hAs : ContDiff ℝ ∞ A) (hAc : HasCompactSupport (fun x => A x - c))
    {L : NNReal} (hA : LipschitzWith L A) {B a : ℝ} (hB : ∀ x, ‖A x‖ ≤ B) (ha : 0 < a)
    (hgard : ∀ y : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ∀ v : Lp (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) 2 (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
      a * ‖(Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) v)‖ ^ 2 ≤ ∫ x, inner ℝ (A (x + y) ((Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) v) x)) ((Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) v) x))
    (hAeq : ∀ x ∈ U, A x = h.projectiveLineSobolevCoefficient V e 1 i x)
    (w f : Lp (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) 2 (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) (htest : ∀ q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1), ∀ hq : HasCompactSupport q, ∀ hqU : tsupport q ⊆ U,
      h.projectiveBochnerL2TestFunctional V e he i q hq (hqU.trans hUD) w = inner ℝ f (q.toLp 2 volume))
    (hf : MemSobolev (n : ℝ) 2 (f : 𝓢'(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)))
    (hprevious : ∀ g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ), HasCompactSupport g →
      (∀ x, g x = Complex.ofReal (g x).re) → tsupport g ⊆ U →
      MemSobolev ((n : ℝ) + 1) 2 ((ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (Analysis.HodgeTheory.Decomposition.VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g w)) : 𝓢'(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)))
    (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g) (hreal : ∀ x, g x = Complex.ofReal (g x).re)
    (hgU : tsupport g ⊆ U) :
    MemSobolev ((n : ℝ) + 2) 2 ((ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (Analysis.HodgeTheory.Decomposition.VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g w)) : 𝓢'(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)) := by
  obtain ⟨ψ, hψc, hψU, hψreal, T, _hT, hKT, hTU, hψT⟩ := Analysis.HodgeTheory.Decomposition.NestedCutoffNeighborhood.Constructions.exists_nested_schwartz_cutoff hg hU hgU
  have hnew (q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)) (hq : HasCompactSupport q) (hqT : tsupport q ⊆ T) :
      h.projectiveBochnerL2TestFunctional V e he i q hq (hqT.trans (hTU.trans hUD))
        (Analysis.HodgeTheory.Decomposition.VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 ψ w) = inner ℝ f (q.toLp 2 volume) :=
    (h.projectiveBochnerL2TestFunctional_nested V e he i q hq (hqT.trans (hTU.trans hUD))
      ψ (fun x hx => hψT x (hqT hx)) w).trans (htest q hq (hqT.trans hTU))
  have hgain := h.projectiveBochner_local_gain V e he i η hη hηc hηU T (hTU.trans hUD)
    (fun x hx => hηone x (hTU hx)) n A c hAs hAc hA hB ha hgard (fun x hx => hAeq x (hTU hx))
    (Analysis.HodgeTheory.Decomposition.VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 ψ w) f hnew (hprevious ψ hψc hψreal hψU) hf g hg hreal hKT
  rw [Analysis.HodgeTheory.Decomposition.VectorNestedCutoffs.Constructions.vectorSobolevCutoffCLM_nested 1 g ψ (fun x hx => hψT x (hKT hx)) w] at hgain
  exact hgain

end

/-! Smooth forcing in the original local Bochner equation gives every Sobolev order by the proved nested-cutoff induction. -/

open _root_.TopologicalSpace _root_.MeasureTheory TemperedDistribution
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.NestedCutoffNeighborhood.Constructions

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveBochner_all_orders (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (U : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (hU : IsOpen U) (hUD : U ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) (hηone : ∀ x ∈ U, η x = 1)
    (A : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1 →L[ℝ] GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (c : GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1 →L[ℝ] GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)
    (hAs : ContDiff ℝ ∞ A) (hAc : HasCompactSupport (fun x => A x - c))
    {L : NNReal} (hA : LipschitzWith L A) {B a : ℝ} (hB : ∀ x, ‖A x‖ ≤ B) (ha : 0 < a)
    (hgard : ∀ y : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ∀ v : Lp (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) 2 (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
      a * ‖(Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) v)‖ ^ 2 ≤ ∫ x, inner ℝ (A (x + y) ((Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) v) x)) ((Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) v) x))
    (hAeq : ∀ x ∈ U, A x = h.projectiveLineSobolevCoefficient V e 1 i x)
    (w f : Lp (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) 2 (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) (htest : ∀ q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1), ∀ hq : HasCompactSupport q, ∀ hqU : tsupport q ⊆ U,
      h.projectiveBochnerL2TestFunctional V e he i q hq (hqU.trans hUD) w = inner ℝ f (q.toLp 2 volume))
    (hf : ∀ n : ℕ, MemSobolev (n : ℝ) 2 (f : 𝓢'(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)))
    (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g) (hreal : ∀ x, g x = Complex.ofReal (g x).re)
    (hgU : tsupport g ⊆ U) :
    ∀ n : ℕ, MemSobolev (n : ℝ) 2 ((ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (Analysis.HodgeTheory.Decomposition.VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g w)) : 𝓢'(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)) := by
  have horders : ∀ n : ℕ, ∀ q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ), HasCompactSupport q →
      (∀ x, q x = Complex.ofReal (q x).re) → tsupport q ⊆ U →
      MemSobolev ((n : ℝ) + 1) 2 ((ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (Analysis.HodgeTheory.Decomposition.VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 q w)) : 𝓢'(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)) := by
    intro n
    induction n with
    | zero =>
      intro q _ _ _
      simpa only [Nat.cast_zero, zero_add] using
        Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange.Constructions.vectorSobolevL2Embedding_memSobolev (by norm_num : (0 : ℝ) ≤ 1) (Analysis.HodgeTheory.Decomposition.VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 q w)
    | succ n ih =>
      intro q hq hqr hqU
      have hnext := h.projectiveBochner_order_step V e he i η hη hηc hηU U hU hUD hηone n
        A c hAs hAc hA hB ha hgard hAeq w f htest (hf n) ih q hq hqr hqU
      simpa only [Nat.cast_succ, add_assoc, one_add_one_eq_two] using hnext
  intro n
  exact (horders n g hg hreal hgU).mono (le_add_of_nonneg_right zero_le_one)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
