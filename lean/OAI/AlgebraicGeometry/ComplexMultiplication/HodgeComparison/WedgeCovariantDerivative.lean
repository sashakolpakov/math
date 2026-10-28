import OAI.AlgebraicTopology.Kunneth.WedgeAlgebra
import OAI.Analysis.HodgeTheory.Decomposition.CovectorConnection

/-! # Wedge Covariant Derivative -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.WedgeCovariantDerivative

noncomputable section

/-! The genuine covector connection obeys the exterior-product rule.
In particular, the exterior product of parallel covectors is parallel. -/

open OAI.AlgebraicTopology.Kunneth.WedgeAlgebra.Constructions OAI.Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace CM.Construction

variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D] {p q : ℕ}

theorem covectorWedge_fderiv {a : D → Analysis.DifferentialForms.Manifold.Basic.FormValue E p} {b : D → Analysis.DifferentialForms.Manifold.Basic.FormValue E q} {x : D}
    (ha : ContDiffAt ℝ 1 a x) (hb : ContDiffAt ℝ 1 b x) (u : D) :
    fderiv ℝ (fun y => AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (a y) (b y)) x u =
      AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (fderiv ℝ a x u) (b x) + AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (a x) (fderiv ℝ b x u) := by
  have had := ha.differentiableAt (by simp)
  have hbd := hb.differentiableAt (by simp)
  have hw : DifferentiableAt ℝ (fun y => AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (a y) (b y)) x :=
    (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.contDiffAt_covectorWedge ha hb).differentiableAt (by simp)
  ext v
  rw [← fderiv_continuousAlternatingMap_apply_const_apply hw,
    AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.covectorWedge_fderiv_apply had hbd]
  change _ = AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (fderiv ℝ a x u) (b x) v +
    AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (a x) (fderiv ℝ b x u) v
  rw [AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.covectorWedge_eq_alternatingSum, AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.covectorWedge_eq_alternatingSum,
    ← smul_add, ← AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum_add]
  rfl

theorem covectorPullback_fderiv_id (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (A : E →L[ℝ] E) :
    fderiv ℝ (fun T : E →L[ℝ] E => a.compContinuousLinearMap T)
      (ContinuousLinearMap.id ℝ E) A = Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction n A a := by
  have h := (hasFDerivAt_const a (ContinuousLinearMap.id ℝ E)).continuousAlternatingMapCompContinuousLinearMap
    (hasFDerivAt_id (ContinuousLinearMap.id ℝ E))
  simp only [ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.comp_id] at h
  exact congrArg (fun L => L A) h.fderiv

theorem covectorInfinitesimalAction_wedge (A : E →L[ℝ] E)
    (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E p) (b : Analysis.DifferentialForms.Manifold.Basic.FormValue E q) :
    Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction (p + q) A (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge a b) =
      AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction p A a) b +
        AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge a (Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction q A b) := by
  have ha : ContDiffAt ℝ 1 (fun T : E →L[ℝ] E => a.compContinuousLinearMap T)
      (ContinuousLinearMap.id ℝ E) :=
    Analysis.DifferentialForms.Manifold.Alternatization.contDiffAt_alternating_compContinuousLinearMap contDiffAt_const contDiffAt_id
  have hb : ContDiffAt ℝ 1 (fun T : E →L[ℝ] E => b.compContinuousLinearMap T)
      (ContinuousLinearMap.id ℝ E) :=
    Analysis.DifferentialForms.Manifold.Alternatization.contDiffAt_alternating_compContinuousLinearMap contDiffAt_const contDiffAt_id
  have h := covectorWedge_fderiv ha hb A
  have he : (fun T : E →L[ℝ] E => AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (a.compContinuousLinearMap T) (b.compContinuousLinearMap T)) =
      (fun T : E →L[ℝ] E => (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge a b).compContinuousLinearMap T) :=
    funext (fun T => AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge_pullback T a b)
  rw [he, covectorPullback_fderiv_id, covectorPullback_fderiv_id, covectorPullback_fderiv_id] at h
  have hi (n : ℕ) (c : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) : c.compContinuousLinearMap (ContinuousLinearMap.id ℝ E) = c := by
    ext v
    rfl
  rw [hi, hi] at h
  exact h

theorem covectorConnectionDerivative_wedge_parallel
    (Γ : E → E →L[ℝ] E →L[ℝ] E) {a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E p} {b : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E q} {x : E}
    (ha : ContDiffAt ℝ 1 a x) (hb : ContDiffAt ℝ 1 b x)
    (hpa : Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorConnectionDerivative p Γ a x = 0)
    (hpb : Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorConnectionDerivative q Γ b x = 0) :
    Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorConnectionDerivative (p + q) Γ (fun y => AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (a y) (b y)) x = 0 := by
  ext u
  have hap : fderiv ℝ a x u = Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction p (Γ x u) (a x) := by
    have h := congrArg (fun L : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E p => L u) hpa
    exact sub_eq_zero.mp h
  have hbp : fderiv ℝ b x u = Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction q (Γ x u) (b x) := by
    have h := congrArg (fun L : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E q => L u) hpb
    exact sub_eq_zero.mp h
  rw [Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorConnectionDerivative_apply, covectorWedge_fderiv ha hb, hap, hbp,
    covectorInfinitesimalAction_wedge, sub_self]
  rfl

end CM.Construction

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.WedgeCovariantDerivative
