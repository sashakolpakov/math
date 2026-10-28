import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Data
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.GlobalCurvature

/-! # Curvature -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric

noncomputable section

/-! Actual global curvature for any smooth positive metric on the original line bundle. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M] {u : Holomorphic.Connecting.holomorphicUnitCohomology E M}

def Data.HolomorphicLineMetricData.logFunction (h : Data.HolomorphicLineMetricData u) (i : M) :
    SmoothScalarForm.SmoothComplexOpenFunction (E := E) (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) :=
  ⟨fun x => (Real.log (h.weight i x) : ℂ), Complex.ofRealCLM.contDiff.contMDiff.comp (fun x =>
    (Real.contDiffAt_log.mpr (ne_of_gt (h.positive i x))).contMDiffAt.comp x (h.smooth i x))⟩

omit [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem Data.HolomorphicLineMetricData.logFunction_transition (h : Data.HolomorphicLineMetricData u)
    (i j x : M) (hi : x ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i)
    (hj : x ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j) :
    h.logFunction i ⟨x, hi⟩ - h.logFunction j ⟨x, hj⟩ =
      (Real.log (Complex.normSq ((Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val ⟨x, hi, hj⟩)) : ℂ) := by
  change (Real.log (h.weight i ⟨x, hi⟩) : ℂ) - (Real.log (h.weight j ⟨x, hj⟩) : ℂ) = _
  rw [h.transition i j x hi hj, Real.log_mul
    (ne_of_gt (Complex.normSq_pos.mpr (Holomorphic.SlitLog.holomorphicUnit_value_ne_zero
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j) ⟨x, hi, hj⟩))) (ne_of_gt (h.positive j ⟨x, hj⟩)),
    Complex.ofReal_add, add_sub_cancel_right]

def Data.HolomorphicLineMetricData.localCurvature (h : Data.HolomorphicLineMetricData u) (i : M) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) 2 :=
  ScalarOpenConnection.smoothScalarOpenCurvature (h.logFunction i)

theorem Data.HolomorphicLineMetricData.localCurvature_closed (h : Data.HolomorphicLineMetricData u) (i : M) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (h.localCurvature i) = 0 := Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d_squared _

theorem Data.HolomorphicLineMetricData.localCurvature_type (h : Data.HolomorphicLineMetricData u) (i : M) :
    Open.ManifoldBidegree.OpenManifoldHasBidegree 1 1 (h.localCurvature i) :=
  OneFormMixedDerivative.openManifold_d_holomorphic_d_mixed (SmoothScalarForm.smoothScalarOpenZeroForm (h.logFunction i))

theorem Data.HolomorphicLineMetricData.localCurvature_overlap (h : Data.HolomorphicLineMetricData u) (i j : M) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict inf_le_left (h.localCurvature i) =
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict inf_le_right (h.localCurvature j) := by
  unfold Data.HolomorphicLineMetricData.localCurvature
  rw [ScalarOpenConnection.smoothScalarOpenCurvature_restrict, ScalarOpenConnection.smoothScalarOpenCurvature_restrict]
  exact LogNormCurvatureVanishing.smoothScalarOpenCurvature_eq_of_logNormSq_difference (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j)
    _ _ (fun x => h.logFunction_transition i j x.val x.property.1 x.property.2)

theorem Data.HolomorphicLineMetricData.localCurvature_compatible (h : Data.HolomorphicLineMetricData u) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.Compatible h.localCurvature :=
  (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.compatible_iff_restrict _).mpr h.localCurvature_overlap

def Data.HolomorphicLineMetricData.curvature (h : Data.HolomorphicLineMetricData u) : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 2 :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.glue (fun _ => le_top)
    (Holomorphic.GlobalCurvature.holomorphicLineCurvature_cover u) h.localCurvature h.localCurvature_compatible)

theorem Data.HolomorphicLineMetricData.curvature_onOpen (h : Data.HolomorphicLineMetricData u) (i : M) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) h.curvature = h.localCurvature i := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  change h.curvature x.val = h.localCurvature i x
  rw [Data.HolomorphicLineMetricData.curvature, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal_apply]
  exact Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.glue_apply (fun _ => le_top) (Holomorphic.GlobalCurvature.holomorphicLineCurvature_cover u)
    h.localCurvature h.localCurvature_compatible ⟨x.val, mem_univ x.val⟩ i x.property

theorem Data.HolomorphicLineMetricData.curvature_closed (h : Data.HolomorphicLineMetricData u) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d h.curvature = 0 := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  have he : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u x)
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d h.curvature) = 0 := by
    rw [← Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen_d, h.curvature_onOpen, h.localCurvature_closed]
  exact congrArg (fun a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u x) 3 =>
    a ⟨x, (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x⟩) he

theorem Data.HolomorphicLineMetricData.curvature_type (h : Data.HolomorphicLineMetricData u) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 1 1 h.curvature.val := by
  intro e he y hy
  let i := e.symm y
  have hi : e.symm y ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i :=
    (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain i
  have hc : (h.localCurvature i).extension.inChart e y = h.curvature.val.inChart e y := by
    rw [← h.curvature_onOpen i]
    unfold Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart
    rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply _ ⟨e.symm y, hi⟩]
    rfl
  rw [← hc]
  exact h.localCurvature_type i e he y ⟨hy, hi⟩

theorem Data.HolomorphicLineMetricData.curvature_tangentType (h : Data.HolomorphicLineMetricData u) :
    Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree E M 1 1 h.curvature.val :=
  (Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree _).mp h.curvature_type

variable [FiniteDimensional ℝ E] [CompactSpace M] [T2Space M]

theorem Curvature.holomorphicLineCanonicalMetric_localCurvature (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (i : M) :
    (Data.holomorphicLineCanonicalMetric u).localCurvature i = HolomorphicLine.LocalCurvature.holomorphicLineLocalCurvatureForm u i := rfl

theorem Curvature.holomorphicLineCanonicalMetric_curvature (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) :
    (Data.holomorphicLineCanonicalMetric u).curvature = Holomorphic.GlobalCurvature.holomorphicLineGlobalCurvature u := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  have he : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u x)
      (Data.holomorphicLineCanonicalMetric u).curvature =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u x) (Holomorphic.GlobalCurvature.holomorphicLineGlobalCurvature u) := by
    rw [Data.HolomorphicLineMetricData.curvature_onOpen, Holomorphic.GlobalCurvature.holomorphicLineGlobalCurvature_onOpen,
      Curvature.holomorphicLineCanonicalMetric_localCurvature]
  exact congrArg (fun a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u x) 2 =>
    a ⟨x, (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x⟩) he

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric
