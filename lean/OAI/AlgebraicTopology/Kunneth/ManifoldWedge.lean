import OAI.AlgebraicTopology.Kunneth.CovectorWedge
import OAI.Analysis.DifferentialForms.Manifold.CovectorAction

/-! # Manifold Wedge -/

namespace OAI.AlgebraicTopology.Kunneth.ManifoldWedge

noncomputable section

/-! Exterior multiplication of actual smooth manifold covectors, preserving pure type. -/

set_option backward.isDefEq.respectTransparency false

open scoped _root_.Manifold ContDiff

namespace Constructions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {p q : ℕ}

local instance manifoldWedgeTangentNormedGroup (x : M) : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) :=
  inferInstanceAs (NormedAddCommGroup E)

local instance manifoldWedgeTangentNormedSpace (x : M) : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) :=
  inferInstanceAs (NormedSpace ℝ E)

def rawManifoldWedge (a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M p) (b : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M q) :
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q) := fun x => CovectorWedge.Constructions.covectorWedge (a x) (b x)

theorem rawManifoldWedge_inChart (a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M p)
    (b : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M q) (e : OpenPartialHomeomorph M E) :
    (rawManifoldWedge a b).inChart e =
      fun y => CovectorWedge.Constructions.covectorWedge (a.inChart e y) (b.inChart e y) := by
  funext y
  exact (CovectorWedge.Constructions.covectorWedge_pullback _ _ _).symm

theorem isSmoothManifoldFormOn_wedge {a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M p}
    {b : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M q} {U : Set M}
    (ha : Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn a U) (hb : Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn b U) :
    Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn (rawManifoldWedge a b) U := by
  intro e he
  rw [rawManifoldWedge_inChart]
  exact CovectorWedge.Constructions.contDiffOn_covectorWedge (ha e he) (hb e he)

/-- The standard exterior product of smooth manifold forms. -/
def manifoldWedge (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p) (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M q) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (p + q) :=
  ⟨rawManifoldWedge a.val b.val, isSmoothManifoldFormOn_wedge a.smooth b.smooth⟩

@[simp] theorem manifoldWedge_apply
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M p) (b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M q) (x : M) :
    manifoldWedge a b x = CovectorWedge.Constructions.covectorWedge (a x) (b x) := rfl

def rawManifoldDegreeCast {n m : ℕ} (h : n = m) (a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M n) :
    Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M m := fun x => CovectorWedge.Constructions.covectorDegreeCast h (a x)

theorem rawManifoldDegreeCast_eq_cast {n m : ℕ} (h : n = m)
    (a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M n) :
    rawManifoldDegreeCast h a = cast (congrArg (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M) h) a := by
  subst m
  rfl

theorem rawManifoldDegreeCast_inChart {n m : ℕ} (h : n = m)
    (a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M n) (e : OpenPartialHomeomorph M E) :
    (rawManifoldDegreeCast h a).inChart e = fun y => CovectorWedge.Constructions.covectorDegreeCast h (a.inChart e y) := by
  subst m
  rfl

theorem isSmoothManifoldFormOn_degreeCast {n m : ℕ} (h : n = m)
    {a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M n} {U : Set M} (ha : Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn a U) :
    Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn (rawManifoldDegreeCast h a) U := by
  subst m
  exact ha

def manifoldDegreeCast {n m : ℕ} (h : n = m) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M n) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M m :=
  ⟨rawManifoldDegreeCast h a.val, isSmoothManifoldFormOn_degreeCast h a.smooth⟩

/-- The product of pure smooth forms has the sum of their two Hodge bidegrees. -/
theorem hasManifoldBidegree_wedge [NormedSpace ℂ E] {p q r s : ℕ}
    {a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q)} {b : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (r + s)}
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M p q a) (hb : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M r s b) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M (p + r) (q + s)
      (rawManifoldDegreeCast (add_add_add_comm p q r s) (rawManifoldWedge a b)) := by
  intro e he y hy
  rw [rawManifoldDegreeCast_inChart, rawManifoldWedge_inChart]
  exact CovectorWedge.Constructions.hasBidegree_covectorWedge _ _ (ha e he y hy) (hb e he y hy)

/-- The same statement in the intrinsic inverse-character convention of Kunneth. -/
theorem hasTangentBidegree_wedge [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    [IsManifold 𝓘(ℂ, E) ∞ M] {p q r s : ℕ}
    {a : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (p + q)} {b : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M (r + s)}
    (ha : Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree E M p q a) (hb : Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree E M r s b) :
    Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree E M (p + r) (q + s)
      (rawManifoldDegreeCast (add_add_add_comm p q r s) (rawManifoldWedge a b)) :=
  (Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree _).mp (hasManifoldBidegree_wedge
    ((Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree a).mpr ha)
    ((Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree b).mpr hb))

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.ManifoldWedge
