import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveBochner.AllOrders
import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveBochner.OpenTests
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ForcingSobolev
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.Bochner

/-! # All Orders -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.AllOrders

noncomputable section

/-! The original Green solution with original smooth forcing has every local Sobolev order on a region with constructed frame and coefficient cutoffs. -/

open _root_.TopologicalSpace _root_.MeasureTheory TemperedDistribution
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Holomorphic.EnergyContinuousExt.smoothCore_fullNormedSpace Holomorphic.EnergyContinuousExt.smoothCore_fullInnerProductSpace
  Holomorphic.EnergyContinuousExt.smoothCore_normedSpace Holomorphic.EnergyContinuousExt.smoothCore_innerProductSpace

abbrev holomorphicMetricSmoothGreen_local_all_orders (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    (τ : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hτ : HasCompactSupport τ) (hτD : tsupport τ ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (hc : h.smoothDolbeaultOneCoercive V)
    (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) (hηone : ∀ x ∈ tsupport τ, η x = 1)
    (U : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) (hU : IsOpen U) (hUD : U ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) (hτU : ∀ x ∈ U, τ x = 1)
    (A : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1 →L[ℝ] GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (c : GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1 →L[ℝ] GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)
    (hAs : ContDiff ℝ ∞ A) (hAc : HasCompactSupport (fun x => A x - c))
    {L : NNReal} (hA : LipschitzWith L A) {B a : ℝ} (hB : ∀ x, ‖A x‖ ≤ B) (ha : 0 < a)
    (hgard : ∀ y : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ∀ v : Lp (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) 2 (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
      a * ‖(Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) v)‖ ^ 2 ≤ ∫ x, inner ℝ (A (x + y) ((Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) v) x)) ((Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) v) x))
    (hAeq : ∀ x ∈ U, A x = h.projectiveLineSobolevCoefficient V e 1 i x)
    (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g) (hreal : ∀ x, g x = Complex.ofReal (g x).re)
    (hgU : tsupport g ⊆ U) (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)  :=
  h.projectiveBochner_all_orders V e he i η hη hηc hηU U hU hUD
    (fun x hx => hηone x (subset_tsupport τ (ne_of_eq_of_ne (hτU x hx) one_ne_zero)))
    A c hAs hAc hA hB ha hgard hAeq (HolomorphicFrame.FrameLocalization.holomorphicMetricFrameH1Localization V h e he i (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff V u e he i τ hτ hτD) (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_smooth V u e he i τ hτ hτD) (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_support V u e he i τ hτ hτD) (HolomorphicSmooth.Green.holomorphicMetricSmoothWeakSolution V h (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a))) (h.projectiveLineForcingL2 V e he i η hη hηc hηU (HolomorphicFrame.Localization.holomorphicMetricFrameL2Localization V h e he i 1 (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff V u e he i τ hτ hτD) (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_smooth V u e he i τ hτ hτD) (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_support V u e he i τ hτ hτD) ((h.antiOneL2Submodule V).subtypeL (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a))))
    (h.projectiveBochner_open_tests V e he i τ hτ hτD (HolomorphicFrame.FrameLocalization.holomorphicMetricFrameH1Localization V h e he i (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff V u e he i τ hτ hτD) (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_smooth V u e he i τ hτ hτD) (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_support V u e he i τ hτ hτD) (HolomorphicSmooth.Green.holomorphicMetricSmoothWeakSolution V h (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a))) (h.projectiveLineForcingL2 V e he i η hη hηc hηU (HolomorphicFrame.Localization.holomorphicMetricFrameL2Localization V h e he i 1 (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff V u e he i τ hτ hτD) (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_smooth V u e he i τ hτ hτD) (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_support V u e he i τ hτ hτD) ((h.antiOneL2Submodule V).subtypeL (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a))))
      (fun q => Bochner.holomorphicMetricSmoothGreen_bochner_L2_equation V h e he i τ hτ hτD hc q η hη hηc hηU hηone (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a))
      U hUD hτU)
    (fun n => h.projectiveLineForcingL2_smooth_source V e he i η hη hηc hηU (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff V u e he i τ hτ hτD) (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_smooth V u e he i τ hτ hτD) (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_support V u e he i τ hτ hτD) a n)
    g hg hreal hgU

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.AllOrders
