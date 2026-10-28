import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.FrameInsertion
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AntiSchwartzTests
import OAI.Analysis.HodgeTheory.Decomposition.ChartTestAbsorption

/-! # Chart Insertion -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ChartInsertion

noncomputable section

/-! Bounded reconstruction of Euclidean L² coefficients into the original bundle, agreeing with the actual smooth frame insertion. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.ChartTestAbsorption.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
  (n : ℕ) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
  (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))

def holomorphicMetricChartL2Insertion :
    Lp (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) 2 (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) →L[ℂ]
      IntegralPairZero.HolomorphicFormL2With V h n :=
  (HolomorphicFrame.FrameInsertion.holomorphicMetricFrameL2Insertion V h i n (AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs) (AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs) (fun _ hx => (AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs hx).2)).comp (Analysis.HodgeTheory.Decomposition.ChartTestAbsorption.Constructions.projectiveChartTestL2 V e he n g hg (fun _ hx => (hs hx).1))

theorem holomorphicMetricChartL2Insertion_on_schwartz
    (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n)) :
    holomorphicMetricChartL2Insertion V h e he i n g hg hs (c.toLp 2 volume) =
      IntegralPairZero.holomorphicFormL2WithInclusion V h n (AntiSchwartzTests.holomorphicLineSchwartzFrameInsertion V u e he i g hg hs n c) :=
  Eq.trans (congrArg (HolomorphicFrame.FrameInsertion.holomorphicMetricFrameL2Insertion V h i n (AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs) (AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs) (fun _ hx => (AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs hx).2)) (Analysis.HodgeTheory.Decomposition.ChartTestAbsorption.Constructions.projectiveChartTestL2_on_schwartz V e he n g hg (fun _ hx => (hs hx).1) c))
    (HolomorphicFrame.FrameInsertion.holomorphicMetricFrameL2Insertion_on_smooth V h i n (AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs) (AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs) (fun _ hx => (AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs hx).2)
      (Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized V e he n g hg (fun _ hx => (hs hx).1) c))

theorem holomorphicMetricChartL2Insertion_absorb (k : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ))
    (hk : ∀ x ∈ tsupport g, k x = 1)
    (v : Lp (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) 2 (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) :
    holomorphicMetricChartL2Insertion V h e he i n g hg hs (ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply k v) =
      holomorphicMetricChartL2Insertion V h e he i n g hg hs v :=
  congrArg (HolomorphicFrame.FrameInsertion.holomorphicMetricFrameL2Insertion V h i n (AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs) (AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs) (fun _ hx => (AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs hx).2)) (Analysis.HodgeTheory.Decomposition.ChartTestAbsorption.Constructions.projectiveChartTestL2_absorb V e he n g hg (fun _ hx => (hs hx).1) k hk v)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ChartInsertion
