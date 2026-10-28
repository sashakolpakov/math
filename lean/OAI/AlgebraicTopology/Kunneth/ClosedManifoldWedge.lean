import OAI.AlgebraicTopology.Kunneth.ManifoldWedge
import OAI.AlgebraicTopology.Kunneth.WedgeAlternating
import OAI.Analysis.DifferentialForms.Manifold.ManifoldDeRham

/-! # Closed Manifold Wedge -/

namespace OAI.AlgebraicTopology.Kunneth.ClosedManifoldWedge

noncomputable section

/-! Closed pure forms are closed under the standard exterior product. -/

set_option backward.isDefEq.respectTransparency false

open scoped _root_.Manifold ContDiff

namespace Constructions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {p q : ℕ}

/-- The product of closed smooth manifold forms is closed. -/
theorem manifoldWedge_d_eq_zero
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p) (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M q)
    (ha : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0) (hb : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d b = 0) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ManifoldWedge.Constructions.manifoldWedge a b) = 0 := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  let e := chartAt E x
  have he : e ∈ atlas E M := chart_mem_atlas E x
  have hx : e x ∈ e.target := e.map_source (mem_chart_source E x)
  have had : extDeriv (a.val.inChart e) (e x) = 0 := by
    have h := a.d_inChart e he hx
    rw [ha] at h
    change (0 : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + 1)).inChart e (e x) = _ at h
    rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_zero] at h
    exact h.symm
  have hbd : extDeriv (b.val.inChart e) (e x) = 0 := by
    have h := b.d_inChart e he hx
    rw [hb] at h
    change (0 : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (q + 1)).inChart e (e x) = _ at h
    rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_zero] at h
    exact h.symm
  have hzero := WedgeAlternating.Constructions.extDeriv_covectorWedge_eq_zero (a.val.inChart e) (b.val.inChart e) (e x)
    ((Analysis.DifferentialForms.Manifold.Derivative.smoothForm_contDiffAt_inChart a.smooth e he hx).of_le (by simp))
    ((Analysis.DifferentialForms.Manifold.Derivative.smoothForm_contDiffAt_inChart b.smooth e he hx).of_le (by simp)) had hbd
  ext v
  change extDeriv ((ManifoldWedge.Constructions.rawManifoldWedge a.val b.val).inChart e) (e x)
    (fun i => Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e x (v i)) = 0
  rw [ManifoldWedge.Constructions.rawManifoldWedge_inChart, hzero]
  rfl

def closedManifoldWedge (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M p) (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M q) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M (p + q) :=
  ⟨ManifoldWedge.Constructions.manifoldWedge a.val b.val, manifoldWedge_d_eq_zero a.val b.val a.property b.property⟩

theorem manifoldDegreeCast_d_eq_zero {n m : ℕ} (h : n = m)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) (ha : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a = 0) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ManifoldWedge.Constructions.manifoldDegreeCast h a) = 0 := by
  subst m
  exact ha

def closedManifoldDegreeCast {n m : ℕ} (h : n = m) (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M n) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M m :=
  ⟨ManifoldWedge.Constructions.manifoldDegreeCast h a.val, manifoldDegreeCast_d_eq_zero h a.val a.property⟩

/-- The actual closed pure representative of a product of two closed pure forms. -/
theorem closedManifoldWedge_hasTangentBidegree
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M]
    {p q r s : ℕ} (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M (p + q))
    (b : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M (r + s))
    (ha : Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree E M p q a.val.val)
    (hb : Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree E M r s b.val.val) :
    Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree E M (p + r) (q + s)
      (closedManifoldDegreeCast (add_add_add_comm p q r s)
        (closedManifoldWedge a b)).val.val :=
  ManifoldWedge.Constructions.hasTangentBidegree_wedge ha hb

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.ClosedManifoldWedge
