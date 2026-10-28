import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SmoothTopology
import Mathlib.Topology.UniformSpace.CompactConvergence

/-! # Smooth Convergence -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SmoothConvergence.CM

noncomputable section

/-! ThetaCycle: intrinsic derivative criterion for convergence of the actual smooth forms. -/

open scoped _root_.Manifold ContDiff _root_.Topology
open Set Filter

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {n : ℕ}

theorem tendsto_smooth_iff {P : Type*} (l : Filter P)
    (forms : P → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    let _ := SmoothTopology.CM.smoothFormTopology E M n
    Tendsto forms l (𝓝 form) ↔ ∀ (e : SmoothTopology.CM.SmoothAtlasChart E M) (m : ℕ),
      Tendsto (fun p => SmoothTopology.CM.smoothChartJet (forms p) e m) l (𝓝 (SmoothTopology.CM.smoothChartJet form e m)) := by
  let _ := SmoothTopology.CM.smoothFormTopology E M n
  change Tendsto forms l (@nhds _ (TopologicalSpace.induced _ _) form) ↔ _
  rw [nhds_induced, tendsto_comap_iff, tendsto_pi_nhds]
  exact forall_congr' fun e => tendsto_pi_nhds

/-- Convergence is precisely uniform convergence of every actual chart
derivative on every compact subset of each chart target. -/
theorem tendsto_smooth_iff_compact_derivatives {P : Type*} (l : Filter P)
    (forms : P → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    let _ := SmoothTopology.CM.smoothFormTopology E M n
    Tendsto forms l (𝓝 form) ↔ ∀ (e : SmoothTopology.CM.SmoothAtlasChart E M) (m : ℕ)
      (C : Set e.val.target), IsCompact C →
      TendstoUniformlyOn
        (fun p (y : e.val.target) => iteratedFDeriv ℝ m ((forms p).val.inChart e.val) y.val)
        (fun y : e.val.target => iteratedFDeriv ℝ m (form.val.inChart e.val) y.val) l C := by
  let _ := SmoothTopology.CM.smoothFormTopology E M n
  refine (tendsto_smooth_iff l forms form).trans ?_
  apply forall_congr'
  intro e
  apply forall_congr'
  intro m
  exact ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn
    (α := e.val.target) (β := E [×m]→L[ℝ] (E [⋀^Fin n]→L[ℝ] ℂ))
    (F := fun p => SmoothTopology.CM.smoothChartJet (forms p) e m) (f := SmoothTopology.CM.smoothChartJet form e m) (p := l)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SmoothConvergence.CM
