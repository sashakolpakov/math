import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.SymmetryFibers
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberPullbackComposition

/-! # Fixed Fiber Point Symmetry -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.FixedFiberPointSymmetry

noncomputable section

/-! A symmetry fixing a fiber coordinate induces the canonical identity on that test-point fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

variable {S : Scheme.{u}} {E A : Over S} (L : Line.Bundles.LineBundle A.left)
  (g : E ⟶ E) (r : E ⟶ A) (h : g ≫ r = r)

/-- The symmetry comparison on a fixed coordinate disappears after identifying the actual target fiber. -/
theorem atPoint {T : Over S} (q : T ⟶ E) (z : T ⟶ A)
    (hq : q ≫ r = z) (hqg : (q ≫ g) ≫ r = z) :
    Line.SymmetryFibers.atPoint (L.pullback r.left) g (Line.Fibers.fiberPullbackIso L g r r h) q ≪≫
        Line.Fibers.fiberPullbackIso L q r z hq = Line.Fibers.fiberPullbackIso L (q ≫ g) r z hqg := by
  let c := (Scheme.Modules.pullbackComp q.left g.left).app (Line.Fibers.fiber L r)
  have hc := FiberPullbackComposition.fiberIso_comp_exact L g q r r z h hq hqg
  have hs := congrArg (fun e => c.symm ≪≫ e) hc
  have hs' : c.symm ≪≫ ((Scheme.Modules.pullback q.left).mapIso (Line.Fibers.fiberPullbackIso L g r r h) ≪≫
      Line.Fibers.fiberPullbackIso L q r z hq) = Line.Fibers.fiberPullbackIso L (q ≫ g) r z hqg := by
    simpa only [c, Iso.symm_self_id_assoc] using hs
  have he := Line.SymmetryFibers.atPoint_eq (L.pullback r.left) g (Line.Fibers.fiberPullbackIso L g r r h) q
  exact (congrArg (fun e => e ≪≫ Line.Fibers.fiberPullbackIso L q r z hq) he).trans
    ((Iso.trans_assoc _ _ _).trans hs')

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.FixedFiberPointSymmetry
