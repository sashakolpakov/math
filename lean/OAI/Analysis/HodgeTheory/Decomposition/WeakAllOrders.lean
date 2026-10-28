import OAI.Analysis.HodgeTheory.Decomposition.WeakEquationLocalization
import OAI.Analysis.HodgeTheory.Decomposition.LocalAllOrders
import OAI.Analysis.HodgeTheory.Decomposition.SmoothChartForcing

/-! # Weak All Orders -/

namespace OAI.Analysis.HodgeTheory.Decomposition.WeakAllOrders.Constructions

noncomputable section

/-! Actual completed manifold weak Hodge solutions with smooth forcing
have every local Sobolev order on compatible chart localizations. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap ContDiff _root_.Manifold

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)
  (χ : V.analyticSpace → ℝ) (hχ : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ χ)
  (hχs : tsupport χ ⊆ e.source)
  (hbound : ∃ B : ℝ, ∀ a, ‖VectorEnergyLocalization.Constructions.projectiveVectorH1Localization V e he (n + 1) χ hχ hχs a‖ ≤
    B * ‖SmoothEnergyInclusion.Constructions.smoothToProjectiveEnergy V n a‖)
  (η : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η)
  (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
  (τ : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hτc : HasCompactSupport τ)
  (hτs : tsupport τ ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
  (hτreal : ∀ x, τ x = Complex.ofReal (τ x).re)

include hbound hη hηc hηU hτc hτs hτreal in
theorem projectiveWeakHodgeSolution_local_all_orders
    (A : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → GradientCoefficient.Constructions.ProjectiveGradientValues V n →L[ℝ] GradientCoefficient.Constructions.ProjectiveGradientValues V n)
    (c : GradientCoefficient.Constructions.ProjectiveGradientValues V n →L[ℝ] GradientCoefficient.Constructions.ProjectiveGradientValues V n)
    (hAsmooth : ContDiff ℝ ∞ A) (hAc : HasCompactSupport (fun x => A x - c))
    {L : NNReal} (hA : LipschitzWith L A) {C a : ℝ} (hC : ∀ x, ‖A x‖ ≤ C) (ha : 0 < a)
    (hgard : ∀ y : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V,
      ∀ v : Lp (SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 2
        (volume : Measure (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
        a * ‖VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) v‖ ^ 2 ≤
          ∫ x, inner ℝ (A (x + y)
            (VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) v x))
            (VectorGradient.Constructions.vectorSobolevGradient (F := SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) v x))
    (T : Set (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (hTopen : IsOpen T) (hT : T ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    {U : Set V.analyticSpace} (hU : IsOpen U) (hTU : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartAlmostEverywhere.CM.Construction.varietyCompactChartImage V e T ⊆ U)
    (hχU : ∀ x ∈ U, χ x = 1) (hηT : ∀ x ∈ T, η x = 1)
    (hAT : ∀ x ∈ T, A x = GradientCoefficient.Constructions.projectiveHodgeGradientCoefficient V e n x) (hτT : ∀ x ∈ T, τ x = 1)
    (u : EnergyDomain.Constructions.ProjectiveEnergyDomain V n) (f : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    (hsol : WeakEquation.Constructions.IsProjectiveWeakHodgeSolution V n u (Form.Constructions.smoothToProjectiveL2 V (n + 1) f))
    (g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgc : HasCompactSupport g)
    (hgreal : ∀ x, g x = Complex.ofReal (g x).re) (hgT : tsupport g ⊆ T) :
    ∀ s : ℕ, MemSobolev (s : ℝ) 2
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)
        (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g (VectorEnergyLocalization.Constructions.projectiveVectorEnergyH1Localization V e he n χ hχ hχs u)) :
        𝓢'(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))) := by
  apply LocalAllOrders.Constructions.projective_local_hodge_all_orders V e n he η hη hηc hηU A c hAsmooth hAc hA hC ha hgard T hTopen
    (VectorEnergyLocalization.Constructions.projectiveVectorEnergyH1Localization V e he n χ hχ hχs u)
    (ChartTestAbsorption.Constructions.projectiveChartForcingL2 V e he (n + 1) τ hτc hτs (Form.Constructions.smoothToProjectiveL2 V (n + 1) f)) _
    (SmoothChartForcing.Constructions.projectiveChartForcingL2_smooth_memSobolev V e he (n + 1) τ hτc hτs hτreal f) g hgc hgreal hgT
  intro q hqc hqT
  apply WeakEquationLocalization.Constructions.projectiveWeakHodgeSolution_local_test V e he n χ hχ hχs hbound η hη hηc hηU A
    hA.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hC) τ hτc hτs
    u (Form.Constructions.smoothToProjectiveL2 V (n + 1) f) hsol q hqc (hqT.trans hT) hU _ hχU
    (fun x hx => hηT x (hqT hx)) (fun x hx => hAT x (hqT hx)) (fun x hx => hτT x (hqT hx))
  rintro x ⟨z, hz, rfl⟩
  exact hTU ⟨z, hqT hz, rfl⟩

end

end OAI.Analysis.HodgeTheory.Decomposition.WeakAllOrders.Constructions
