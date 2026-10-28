import OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame

/-! # Fiber Point Equality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberPointEquality.Construction

noncomputable section

/-! Equality of actual points transports their line fibers by the
canonical pullback equality isomorphism, preserving global point frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame

universe u

def fiberPointIso {S : Scheme.{u}} {E T : Over S} (L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left)
    (x y : T ⟶ E) (h : x = y) : Picard.PoincareBundle.Line.Fibers.fiber L x ≅ Picard.PoincareBundle.Line.Fibers.fiber L y :=
  (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left h)).app L.sheaf

theorem fiberPointIso_refl {S : Scheme.{u}} {E T : Over S} (L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left)
    (x : T ⟶ E) : fiberPointIso L x x rfl = Iso.refl (Picard.PoincareBundle.Line.Fibers.fiber L x) := rfl

theorem atPoint_congr_target {S : Scheme.{u}} {A E T : Over S} (p : A ⟶ E)
    (L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left) (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A.left ≅ (Scheme.Modules.pullback p.left).obj L.sheaf)
    (a : T ⟶ A) (x y : T ⟶ E) (hx : a ≫ p = x) (hy : a ≫ p = y) (h : x = y) :
    Picard.PoincareBundle.GlobalPullbackFrame.atPoint p L s a x hx ≪≫ fiberPointIso L x y h = Picard.PoincareBundle.GlobalPullbackFrame.atPoint p L s a y hy := by
  cases h
  exact Iso.trans_refl _

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberPointEquality.Construction
