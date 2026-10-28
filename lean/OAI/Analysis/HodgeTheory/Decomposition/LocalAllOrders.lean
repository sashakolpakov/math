import OAI.Analysis.HodgeTheory.Decomposition.LocalGain
import OAI.Analysis.HodgeTheory.Decomposition.NestedEnergy
import OAI.Analysis.HodgeTheory.Decomposition.NestedCutoffNeighborhood

/-! # Local All Orders -/

namespace OAI.Analysis.HodgeTheory.Decomposition.LocalAllOrders.Constructions

noncomputable section

section

/-! Local Hodge regularity improves by one order on all compact cutoffs,
using an intermediate cutoff without changing the actual weak equation. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap ContDiff

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (η : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η)
  (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)

theorem projective_local_hodge_order_step (s : ℕ)
    (A : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → GradientCoefficient.Constructions.ProjectiveGradientValues V n →L[ℝ] GradientCoefficient.Constructions.ProjectiveGradientValues V n)
    (c : GradientCoefficient.Constructions.ProjectiveGradientValues V n →L[ℝ] GradientCoefficient.Constructions.ProjectiveGradientValues V n)
    (hAsmooth : ContDiff ℝ ∞ A) (hAc : HasCompactSupport (fun x => A x - c))
    {L : NNReal} (hL : LipschitzWith L A) {C a : ℝ} (hC : ∀ x, ‖A x‖ ≤ C) (ha : 0 < a)
    (hgard : ∀ y : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V,
      ∀ v : Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2
        (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
        a * ‖VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) v‖ ^ 2 ≤
          ∫ x, inner ℝ (A (x + y)
            (VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) v x))
            (VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) v x))
    (U : Set (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (hU : IsOpen U)
    (u f : Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)))
    (hsol : ∀ q : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V,
        SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)),
      HasCompactSupport q → tsupport q ⊆ U →
        LocalEnergy.Constructions.projectiveLocalHodgeEnergy V e n he η hη hηc hηU A
          hL.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hC) u
          (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 q) = inner ℝ f (q.toLp 2 volume))
    (hf : MemSobolev (s : ℝ) 2
      (f : 𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))))
    (hprevious : ∀ g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ), HasCompactSupport g →
      (∀ x, g x = Complex.ofReal (g x).re) → tsupport g ⊆ U →
      MemSobolev ((s : ℝ) + 1) 2
        (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g u) :
          𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))))
    (g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport g)
    (hgreal : ∀ x, g x = Complex.ofReal (g x).re) (hgU : tsupport g ⊆ U) :
    MemSobolev ((s : ℝ) + 2) 2
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g u) :
        𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))) := by
  obtain ⟨ψ, hψc, hψU, hψreal, T, _hT, hKT, hTU, hψT⟩ := NestedCutoffNeighborhood.Constructions.exists_nested_schwartz_cutoff hgc hU hgU
  have hnew (q : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V,
      SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)))
      (hqc : HasCompactSupport q) (hqT : tsupport q ⊆ T) :
      LocalEnergy.Constructions.projectiveLocalHodgeEnergy V e n he η hη hηc hηU A
        hL.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hC)
        (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 ψ u) (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 q) = inner ℝ f (q.toLp 2 volume) :=
    (NestedEnergy.Constructions.projectiveLocalHodgeEnergy_nested V e n he η hη hηc hηU A
      hL.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hC) ψ q
      (fun x hx => hψT x (hqT hx)) u).trans (hsol q hqc (hqT.trans hTU))
  have hH := LocalGain.Constructions.projective_local_hodge_gain V e n he η hη hηc hηU s A c hAsmooth hAc hL hC ha hgard
    T (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 ψ u) f hnew (hprevious ψ hψc hψreal hψU) hf g hgc hgreal hKT
  rw [VectorNestedCutoffs.Constructions.vectorSobolevCutoffCLM_nested 1 g ψ (fun x hx => hψT x (hKT hx)) u] at hH
  exact hH

end

/-! Smooth local forcing gives all Sobolev orders for the actual local
Hodge equation, using the proved interior regularity step. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap ContDiff

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (η : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η)
  (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)

theorem projective_local_hodge_all_orders
    (A : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → GradientCoefficient.Constructions.ProjectiveGradientValues V n →L[ℝ] GradientCoefficient.Constructions.ProjectiveGradientValues V n)
    (c : GradientCoefficient.Constructions.ProjectiveGradientValues V n →L[ℝ] GradientCoefficient.Constructions.ProjectiveGradientValues V n)
    (hAsmooth : ContDiff ℝ ∞ A) (hAc : HasCompactSupport (fun x => A x - c))
    {L : NNReal} (hL : LipschitzWith L A) {C a : ℝ} (hC : ∀ x, ‖A x‖ ≤ C) (ha : 0 < a)
    (hgard : ∀ y : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V,
      ∀ v : Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2
        (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
        a * ‖VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) v‖ ^ 2 ≤
          ∫ x, inner ℝ (A (x + y)
            (VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) v x))
            (VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) v x))
    (U : Set (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (hU : IsOpen U)
    (u f : Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2
      (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)))
    (hsol : ∀ q : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V,
        SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)),
      HasCompactSupport q → tsupport q ⊆ U →
        LocalEnergy.Constructions.projectiveLocalHodgeEnergy V e n he η hη hηc hηU A
          hL.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hC) u
          (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 q) = inner ℝ f (q.toLp 2 volume))
    (hf : ∀ s : ℕ, MemSobolev (s : ℝ) 2
      (f : 𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))))
    (g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport g)
    (hgreal : ∀ x, g x = Complex.ofReal (g x).re) (hgU : tsupport g ⊆ U) :
    ∀ s : ℕ, MemSobolev (s : ℝ) 2
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g u) :
        𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))) := by
  have horders : ∀ s : ℕ, ∀ g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ), HasCompactSupport g →
      (∀ x, g x = Complex.ofReal (g x).re) → tsupport g ⊆ U →
      MemSobolev ((s : ℝ) + 1) 2
        (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g u) :
          𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))) := by
    intro s
    induction s with
    | zero =>
      intro q _ _ _
      simpa only [Nat.cast_zero, zero_add] using
        VectorEmbeddingRange.Constructions.vectorSobolevL2Embedding_memSobolev (by norm_num : (0 : ℝ) ≤ 1) (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 q u)
    | succ s ih =>
      intro q hqc hqreal hqU
      have h := projective_local_hodge_order_step V e n he η hη hηc hηU s A c hAsmooth hAc hL hC ha hgard
        U hU u f hsol (hf s) ih q hqc hqreal hqU
      simpa only [Nat.cast_succ, add_assoc, one_add_one_eq_two] using h
  intro s
  exact (horders s g hgc hgreal hgU).mono (by linarith)

end

end OAI.Analysis.HodgeTheory.Decomposition.LocalAllOrders.Constructions
