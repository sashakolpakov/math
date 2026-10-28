import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.NestedFrameCutoff
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.SchwartzTestCutoff

/-! # Outer Cutoff Neighborhood -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.OuterCutoffNeighborhood

noncomputable section

section

/-! A genuine real outer cutoff for the actual global antiholomorphic Schwartz tests. -/

open _root_.TopologicalSpace Filter
open scoped _root_.Manifold ContDiff SchwartzMap _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
  (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))

def holomorphicSchwartzOuterFrameCutoff : V.analyticSpace → ℂ :=
  (NestedFrameCutoff.exists_real_outer_holomorphic_frame_cutoff V u e he i (AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs)
    (AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs)).choose

theorem holomorphicSchwartzOuterFrameCutoff_smooth :
    ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ (holomorphicSchwartzOuterFrameCutoff V u e he i g hg hs) :=
  (NestedFrameCutoff.exists_real_outer_holomorphic_frame_cutoff V u e he i (AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs)
    (AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs)).choose_spec.1

theorem holomorphicSchwartzOuterFrameCutoff_support :
    tsupport (holomorphicSchwartzOuterFrameCutoff V u e he i g hg hs) ⊆
      (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace) :=
  (NestedFrameCutoff.exists_real_outer_holomorphic_frame_cutoff V u e he i (AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs)
    (AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs)).choose_spec.2.1

theorem holomorphicSchwartzOuterFrameCutoff_real (x : V.analyticSpace) :
    holomorphicSchwartzOuterFrameCutoff V u e he i g hg hs x =
      Complex.ofReal (holomorphicSchwartzOuterFrameCutoff V u e he i g hg hs x).re :=
  (NestedFrameCutoff.exists_real_outer_holomorphic_frame_cutoff V u e he i (AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs)
    (AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs)).choose_spec.2.2.1 x

theorem holomorphicSchwartzOuterFrameCutoff_near (x : V.analyticSpace)
    (hx : x ∈ tsupport (AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs)) :
    holomorphicSchwartzOuterFrameCutoff V u e he i g hg hs =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) :=
  (NestedFrameCutoff.exists_real_outer_holomorphic_frame_cutoff V u e he i (AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs)
    (AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs)).choose_spec.2.2.2 x hx

theorem holomorphicSchwartzOuterFrameCutoff_one (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ tsupport g) :
    holomorphicSchwartzOuterFrameCutoff V u e he i g hg hs (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) = 1 := by
  have hinner := AntiSchwartzTests.holomorphicSchwartzFrameCutoff_one V u e he i g hg hs z hz
  have ht : Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z ∈ tsupport (AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs) :=
    subset_tsupport _ (fun hzero => one_ne_zero (hinner.symm.trans hzero))
  exact (holomorphicSchwartzOuterFrameCutoff_near V u e he i g hg hs _ ht).eq_of_nhds

theorem holomorphicSchwartzOuterFrameCutoff_fixes_test
    (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)) :
    HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V (holomorphicSchwartzOuterFrameCutoff V u e he i g hg hs)
      (holomorphicSchwartzOuterFrameCutoff_smooth V u e he i g hg hs)
      (AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c) =
        AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c :=
  SchwartzTestCutoff.holomorphicLineCutoffAntiForm_of_fixed_inner V (holomorphicSchwartzOuterFrameCutoff V u e he i g hg hs)
    (holomorphicSchwartzOuterFrameCutoff_smooth V u e he i g hg hs)
    (AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs)
    (AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs)
    (fun x hx => (holomorphicSchwartzOuterFrameCutoff_near V u e he i g hg hs x hx).eq_of_nhds)
    (AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c)
    (SchwartzTestCutoff.holomorphicLineAntiSchwartzFrameInsertion_cutoff_anti V u e he i g hg hs c)

end

/-! Coordinate support at a chart point gives the original constructed outer cutoff identically one on a manifold neighborhood. -/

open _root_.TopologicalSpace Filter
open scoped _root_.Manifold ContDiff SchwartzMap _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem holomorphicSchwartzOuterFrameCutoff_near_of_coordinate_support (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
    (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (x : V.analyticSpace) (hx : x ∈ e.source) (hxs : Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e x ∈ tsupport g) :
    holomorphicSchwartzOuterFrameCutoff V u e he i g hg hs =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) := by
  have hinner := AntiSchwartzTests.holomorphicSchwartzFrameCutoff_one V u e he i g hg hs (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e x) hxs
  rw [Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse_forward V e x hx] at hinner
  exact holomorphicSchwartzOuterFrameCutoff_near V u e he i g hg hs x
    (subset_tsupport _ (ne_of_eq_of_ne hinner one_ne_zero))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.OuterCutoffNeighborhood
