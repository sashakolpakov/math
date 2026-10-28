import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveLine.MetricCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Cutoff

/-! # Frame Scalar Glue -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.FrameScalarGlue

noncomputable section

section

/-! Actual holomorphic line transition functions and bundle-frame compatibility in a fixed original projective chart. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

def projectiveTransitionChart (i j : V.analyticSpace) (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : ℂ :=
  Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension
    (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i ⊓
      Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u j)
    (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition V.analyticModel V.analyticSpace u i j).val)
    (e.symm (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z))

theorem projectiveTransitionChart_apply (i j : V.analyticSpace) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i ⊓
        Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u j)) :
    projectiveTransitionChart V u e i j z =
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition V.analyticModel V.analyticSpace u i j).val
        ⟨e.symm (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z), hz.2⟩ :=
  Analysis.DifferentialForms.Manifold.LocallyConstant.manifoldOpenScalarExtension_apply _ _ ⟨e.symm (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z), hz.2⟩

include he

theorem projectiveTransitionChart_smooth (i j : V.analyticSpace) :
    ContDiffOn ℝ ∞ (projectiveTransitionChart V u e i j)
      (ConnectionChartDerivative.projectiveOpenChartDomain V e
        (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i ⊓
          Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u j) : Set _) :=
  (SmoothScalarForm.smoothOpenScalarExtension_chart_contDiff
    (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition V.analyticModel V.analyticSpace u i j).val) e he).comp
    ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).contDiff.restrict_scalars ℝ).contDiffOn (fun _ hz => hz)

omit he in
theorem holomorphicLineSmoothForm_transition_chart (U : Opens V.analyticSpace) (n : ℕ)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n) (i j : V.analyticSpace) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i ⊓
        Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u j))) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (a.val j).extension z =
      projectiveTransitionChart V u e i j z • Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (a.val i).extension z := by
  rw [projectiveTransitionChart_apply V u e i j ⟨hz.1, hz.2.2⟩]
  unfold Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply (a.val j)
      ⟨e.symm (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z), hz.2.1, hz.2.2.2⟩,
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply (a.val i)
      ⟨e.symm (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z), hz.2.1, hz.2.2.1⟩,
    a.property i j _ hz.2.1 hz.2.2.1 hz.2.2.2]
  ext v
  rfl

end

/-! Compatible scalar expressions in the original line frames glue smoothly throughout a fixed projective chart. -/

open Filter _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)

def projectiveLineScalarGlue (f : V.analyticSpace → ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ)
    (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : ℂ := f (e.symm (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) z

theorem projectiveLineScalarGlue_onOpen (U : Opens V.analyticSpace)
    (f : V.analyticSpace → ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ)
    (hf : ∀ i j z, z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i ⊓
        Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u j)) → f j z = f i z)
    (i : V.analyticSpace) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e
      (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    projectiveLineScalarGlue V e f z = f i z :=
  hf i (e.symm (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)) z
    ⟨hz.1, hz.2.1, hz.2.2, (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts V.analyticModel V.analyticSpace u).mem_domain _⟩

theorem projectiveLineScalarGlue_smooth (U : Opens V.analyticSpace)
    (f : V.analyticSpace → ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ)
    (hf : ∀ i j z, z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i ⊓
        Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u j)) → f j z = f i z)
    (hs : ∀ i, ContDiffOn ℝ ∞ (f i) (ConnectionChartDerivative.projectiveOpenChartDomain V e
      (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) : Set _)) :
    ContDiffOn ℝ ∞ (projectiveLineScalarGlue V e f) (ConnectionChartDerivative.projectiveOpenChartDomain V e U : Set _) := by
  intro z hz
  let i := e.symm (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)
  have hzi : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e
      (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) :=
    ⟨hz.1, hz.2, (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts V.analyticModel V.analyticSpace u).mem_domain i⟩
  have heq : projectiveLineScalarGlue V e f =ᶠ[𝓝 z] f i := by
    filter_upwards [(ConnectionChartDerivative.projectiveOpenChartDomain V e _).isOpen.mem_nhds hzi] with y hy
    exact projectiveLineScalarGlue_onOpen V u e U f hf i hy
  exact (((hs i).contDiffAt ((ConnectionChartDerivative.projectiveOpenChartDomain V e _).isOpen.mem_nhds hzi)).congr_of_eventuallyEq heq).contDiffWithinAt

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.FrameScalarGlue
