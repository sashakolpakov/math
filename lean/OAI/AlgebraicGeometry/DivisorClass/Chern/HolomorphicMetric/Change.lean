import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Curvature
import OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarOpenConnection

/-! # Change -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric

noncomputable section

/-! Changing an actual Hermitian metric changes its curvature by an explicit global boundary. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {u : Holomorphic.Connecting.holomorphicUnitCohomology E M}

def Data.HolomorphicLineMetricData.ratioLogFunction (h k : Data.HolomorphicLineMetricData u) :
    SmoothScalarForm.SmoothComplexOpenFunction (E := E) (⊤ : Opens M) :=
  ⟨fun x => (Real.log (h.ratio k x.val) : ℂ),
    (Complex.ofRealCLM.contDiff.contMDiff.comp (fun x =>
      (Real.contDiffAt_log.mpr (ne_of_gt (h.ratio_positive k x))).contMDiffAt.comp x (h.ratio_smooth k x))).comp
        (contMDiff_subtype_val (I := 𝓘(ℝ, E)))⟩

omit [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem Data.HolomorphicLineMetricData.logFunction_ratio (h k : Data.HolomorphicLineMetricData u) (i : M) :
    h.logFunction i = k.logFunction i + SmoothScalarForm.smoothComplexOpenFunctionRestrict le_top (h.ratioLogFunction k) := by
  apply ContMDiffMap.ext
  intro x
  change (Real.log (h.weight i x) : ℂ) = (Real.log (k.weight i x) : ℂ) + (Real.log (h.ratio k x.val) : ℂ)
  rw [h.ratio_onOpen k i x, Data.HolomorphicLineMetricData.localRatio, Real.log_div (ne_of_gt (h.positive i x)) (ne_of_gt (k.positive i x)),
    Complex.ofReal_sub]
  ring

def Data.HolomorphicLineMetricData.changePrimitive (h k : Data.HolomorphicLineMetricData u) : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1 :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal (ScalarOpenConnection.smoothScalarOpenConnection (h.ratioLogFunction k))

theorem Change.scalarConnection_global_d_onOpen (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) (⊤ : Opens M)) (U : Opens M) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal (ScalarOpenConnection.smoothScalarOpenConnection f))) =
      ScalarOpenConnection.smoothScalarOpenCurvature (SmoothScalarForm.smoothComplexOpenFunctionRestrict le_top f) := by
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal_d]
  have he : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d
      (ScalarOpenConnection.smoothScalarOpenConnection f))) =
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict le_top (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (ScalarOpenConnection.smoothScalarOpenConnection f)) := by
    exact (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.restrict_onOpen (show U ≤ (⊤ : Opens M) from le_top) _).symm.trans
      (congrArg (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (show U ≤ (⊤ : Opens M) from le_top))
        (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.onOpen_toGlobal (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (ScalarOpenConnection.smoothScalarOpenConnection f))))
  exact he.trans (ScalarOpenConnection.smoothScalarOpenCurvature_restrict le_top f)

theorem Data.HolomorphicLineMetricData.localCurvature_change (h k : Data.HolomorphicLineMetricData u) (i : M) :
    h.localCurvature i = k.localCurvature i +
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (h.changePrimitive k)) := by
  unfold Data.HolomorphicLineMetricData.localCurvature
  rw [h.logFunction_ratio k i, ScalarOpenConnection.smoothScalarOpenCurvature_add]
  exact congrArg (fun a => ScalarOpenConnection.smoothScalarOpenCurvature (k.logFunction i) + a)
    (Change.scalarConnection_global_d_onOpen (h.ratioLogFunction k) (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i)).symm

theorem Data.HolomorphicLineMetricData.curvature_change_add (h k : Data.HolomorphicLineMetricData u) :
    h.curvature = k.curvature + Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (h.changePrimitive k) := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  have he : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u x) h.curvature =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u x) k.curvature +
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u x) (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (h.changePrimitive k)) :=
    (h.curvature_onOpen x).trans ((h.localCurvature_change k x).trans
      (congrArg (fun a => a + Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u x)
        (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (h.changePrimitive k))) (k.curvature_onOpen x).symm))
  exact congrArg (fun a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u x) 2 =>
    a ⟨x, (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x⟩) he

theorem Data.HolomorphicLineMetricData.curvature_change (h k : Data.HolomorphicLineMetricData u) :
    h.curvature - k.curvature = Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (h.changePrimitive k) :=
  sub_eq_iff_eq_add.mpr ((h.curvature_change_add k).trans (add_comm _ _))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric
