import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IsoConjugateSquare
import OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalFrameNaturality
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FiberIsomorphisms

/-! # Global Fiber Iso Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GlobalFiberIsoTransport.Construction

noncomputable section

/-! An isomorphism of two global pulled-back lines compares their
actual point fibers naturally under every change of test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame

universe u

variable {S : Scheme.{u}} {K E : Over S} (p q : K ⟶ E)
  (L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left)
  (e : (L.pullback p.left).sheaf ≅ (L.pullback q.left).sheaf)

def globalFiberIsoTransport {T : Over S} (a : T ⟶ K) (x y : T ⟶ E)
    (hx : a ≫ p = x) (hy : a ≫ q = y) : Picard.PoincareBundle.Line.Fibers.fiber L x ≅ Picard.PoincareBundle.Line.Fibers.fiber L y :=
  (Picard.PoincareBundle.GlobalPullbackFrame.comparison p L a x hx).symm ≪≫ (Scheme.Modules.pullback a.left).mapIso e ≪≫ Picard.PoincareBundle.GlobalPullbackFrame.comparison q L a y hy

theorem globalFiberIsoTransport_pullback {T T' : Over S} (f : T' ⟶ T)
    (a : T ⟶ K) (x y : T ⟶ E) (hx : a ≫ p = x) (hy : a ≫ q = y)
    (a' : T' ⟶ K) (x' y' : T' ⟶ E) (hx' : a' ≫ p = x') (hy' : a' ≫ q = y')
    (ha : f ≫ a = a') (hfx : f ≫ x = x') (hfy : f ≫ y = y') :
    (Scheme.Modules.pullback f.left).mapIso (globalFiberIsoTransport p q L e a x y hx hy) ≪≫
      Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L f y y' hfy =
    Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L f x x' hfx ≪≫ globalFiberIsoTransport p q L e a' x' y' hx' hy' := by
  exact IsoConjugateSquare.Construction.iso_map_conjugate_square (Scheme.Modules.pullback f.left)
    (Picard.PoincareBundle.GlobalPullbackFrame.comparison p L a x hx) (Picard.PoincareBundle.GlobalPullbackFrame.comparison q L a y hy) ((Scheme.Modules.pullback a.left).mapIso e)
    (Picard.PoincareBundle.GlobalPullbackFrame.comparison p L a' x' hx') (Picard.PoincareBundle.GlobalPullbackFrame.comparison q L a' y' hy') ((Scheme.Modules.pullback a'.left).mapIso e)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (L.pullback p.left) f a a' ha) (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso (L.pullback q.left) f a a' ha)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L f x x' hfx) (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L f y y' hfy)
    (Picard.PoincareBundle.GlobalFrameNaturality.comparison_pullback p L f a x hx a' x' hx' ha hfx)
    (Picard.PoincareBundle.GlobalFrameNaturality.comparison_pullback q L f a y hy a' y' hy' ha hfy)
    (Picard.PoincareBundle.Line.FiberIsomorphisms.fiberIso_pullback (L.pullback p.left) (L.pullback q.left) e f a a' ha)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GlobalFiberIsoTransport.Construction
