import OAI.Analysis.DifferentialForms.Manifold.Charts
import Mathlib.Topology.ContinuousMap.Compact

/-! # Smooth Topology -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SmoothTopology.CM

noncomputable section

/-!
ThetaCycle: the usual smooth topology on actual manifold forms.

The defining coordinates are all derivatives of all atlas expressions, with
the compact-open topology on each chart target. Thus convergence means uniform
convergence of every derivative on every compact subset of every chart. No
integration or theta-family data enter this topology.
-/

open scoped _root_.Manifold ContDiff _root_.Topology
open Set Filter

variable (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] (n : ℕ)

abbrev SmoothAtlasChart := {e : OpenPartialHomeomorph M E // e ∈ atlas E M}

variable {E M n}

theorem chart_derivative_continuousOn (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (e : SmoothAtlasChart E M) (m : ℕ) :
    ContinuousOn (iteratedFDeriv ℝ m (form.val.inChart e.val)) e.val.target := by
  have h : ContDiffOn ℝ ∞ (form.val.inChart e.val) e.val.target := by
    simpa only [Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain, preimage_univ, inter_univ] using form.property e e.property
  exact (h.continuousOn_iteratedFDerivWithin (m := m) (by exact_mod_cast le_top (a := (m : ℕ∞)))
    e.val.open_target.uniqueDiffOn).congr
    (iteratedFDerivWithin_of_isOpen m e.val.open_target).symm

/-- The actual derivative in an atlas chart, restricted to its open target. -/
def smoothChartJet (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (e : SmoothAtlasChart E M) (m : ℕ) :
    C(e.val.target, E [×m]→L[ℝ] (E [⋀^Fin n]→L[ℝ] ℂ)) :=
  ⟨fun y => iteratedFDeriv ℝ m (form.val.inChart e.val) y.val,
    continuousOn_iff_continuous_domRestrict.mp (chart_derivative_continuousOn form e m)⟩

/-- Initial topology of the genuine chart derivatives in compact-open function spaces. -/
@[instance_reducible]
def smoothFormTopology (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (n : ℕ) :
    TopologicalSpace (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :=
  TopologicalSpace.induced (fun form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n =>
    fun (e : SmoothAtlasChart E M) (m : ℕ) => smoothChartJet form e m) inferInstance

theorem smooth_chart_jet_continuous (e : SmoothAtlasChart E M) (m : ℕ) :
    let _ := smoothFormTopology E M n
    Continuous (fun form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n => smoothChartJet form e m) := by
  let _ := smoothFormTopology E M n
  have h : Continuous (fun form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n =>
      fun (e : SmoothAtlasChart E M) (m : ℕ) => smoothChartJet form e m) :=
    continuous_induced_dom
  exact (continuous_apply m).comp ((continuous_apply e).comp h)

/-- A useful coordinate criterion for continuity into the smooth topology. -/
theorem continuous_smooth_iff {P : Type*} [TopologicalSpace P]
    (forms : P → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    let _ := smoothFormTopology E M n
    Continuous forms ↔ ∀ (e : SmoothAtlasChart E M) (m : ℕ),
      Continuous (fun p => smoothChartJet (forms p) e m) := by
  let _ := smoothFormTopology E M n
  change @Continuous _ _ _ (TopologicalSpace.induced _ _) forms ↔ _
  rw [continuous_induced_rng, continuous_pi_iff]
  exact forall_congr' fun e => continuous_pi_iff

/-- Evaluation of the zero-order chart jet is jointly continuous. -/
theorem smooth_chart_value_continuous [FiniteDimensional ℝ E]
    (e : SmoothAtlasChart E M) :
    let _ := smoothFormTopology E M n
    Continuous (fun p : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n × e.val.target =>
      p.1.val.inChart e.val p.2.val) := by
  let _ := smoothFormTopology E M n
  let : LocallyCompactSpace e.val.target := e.val.open_target.locallyCompactSpace
  have h : Continuous (fun p : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n × e.val.target =>
      smoothChartJet p.1 e 0 p.2) :=
    continuous_eval.comp
      ((smooth_chart_jet_continuous e 0).prodMap continuous_id)
  exact (continuous_eval_const (fun i : Fin 0 => Fin.elim0 i)).comp h

theorem smooth_chart_family_continuousOn [FiniteDimensional ℝ E]
    {P : Type*} [TopologicalSpace P] (e : SmoothAtlasChart E M)
    (forms : P → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n)
    (hforms : let _ := smoothFormTopology E M n; Continuous forms) :
    ContinuousOn (fun p : P × E => (forms p.1).val.inChart e.val p.2)
      (univ ×ˢ e.val.target) := by
  let _ := smoothFormTopology E M n
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hc : Continuous (fun p : (univ ×ˢ e.val.target : Set (P × E)) =>
      (forms p.val.1, (⟨p.val.2, p.property.2⟩ : e.val.target))) :=
    (hforms.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  exact (smooth_chart_value_continuous e).comp hc

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SmoothTopology.CM
