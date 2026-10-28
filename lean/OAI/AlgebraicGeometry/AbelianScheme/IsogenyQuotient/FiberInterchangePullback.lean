import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InterchangePullback
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.InterchangeTransport
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers

/-! # Fiber Interchange Pullback -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberInterchangePullback.Construction

noncomputable section

/-! The actual fiberwise interchange equation is preserved by every
change of test scheme and the canonical fiber comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback

universe u

theorem fiberBilinear_interchange_pullback {S : Scheme.{u}} {E T T' : Over S}
    (L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left) (r : T' ⟶ T)
    (c a b x ca cb ax bx w : T ⟶ E) (c' a' b' x' ca' cb' ax' bx' w' : T' ⟶ E)
    (hc : r ≫ c = c') (ha : r ≫ a = a') (hb : r ≫ b = b') (hx : r ≫ x = x')
    (hca : r ≫ ca = ca') (hcb : r ≫ cb = cb') (hax : r ≫ ax = ax') (hbx : r ≫ bx = bx') (hw : r ≫ w = w')
    (axMap : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L a) (Picard.PoincareBundle.Line.Fibers.fiber L x) (Picard.PoincareBundle.Line.Fibers.fiber L ax))
    (bxMap : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L b) (Picard.PoincareBundle.Line.Fibers.fiber L x) (Picard.PoincareBundle.Line.Fibers.fiber L bx))
    (cbMap : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L c) (Picard.PoincareBundle.Line.Fibers.fiber L b) (Picard.PoincareBundle.Line.Fibers.fiber L cb))
    (caMap : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L c) (Picard.PoincareBundle.Line.Fibers.fiber L a) (Picard.PoincareBundle.Line.Fibers.fiber L ca))
    (byMap : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L cb) (Picard.PoincareBundle.Line.Fibers.fiber L ax) (Picard.PoincareBundle.Line.Fibers.fiber L w))
    (azMap : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L ca) (Picard.PoincareBundle.Line.Fibers.fiber L bx) (Picard.PoincareBundle.Line.Fibers.fiber L w))
    (h : ∀ (U : T.left.Opens) (sc : Γ(Picard.PoincareBundle.Line.Fibers.fiber L c, U)) (sa : Γ(Picard.PoincareBundle.Line.Fibers.fiber L a, U))
      (sb : Γ(Picard.PoincareBundle.Line.Fibers.fiber L b, U)) (sx : Γ(Picard.PoincareBundle.Line.Fibers.fiber L x, U)),
      byMap.app U (cbMap.app U sc sb) (axMap.app U sa sx) = azMap.app U (caMap.app U sc sa) (bxMap.app U sb sx))
    (U : T'.left.Opens) (sc : Γ(Picard.PoincareBundle.Line.Fibers.fiber L c', U)) (sa : Γ(Picard.PoincareBundle.Line.Fibers.fiber L a', U))
    (sb : Γ(Picard.PoincareBundle.Line.Fibers.fiber L b', U)) (sx : Γ(Picard.PoincareBundle.Line.Fibers.fiber L x', U)) :
    (Picard.PoincareBundle.Line.Fibers.pullBilinear L r cb ax w cb' ax' w' hcb hax hw byMap).app U
      ((Picard.PoincareBundle.Line.Fibers.pullBilinear L r c b cb c' b' cb' hc hb hcb cbMap).app U sc sb)
      ((Picard.PoincareBundle.Line.Fibers.pullBilinear L r a x ax a' x' ax' ha hx hax axMap).app U sa sx) =
    (Picard.PoincareBundle.Line.Fibers.pullBilinear L r ca bx w ca' bx' w' hca hbx hw azMap).app U
      ((Picard.PoincareBundle.Line.Fibers.pullBilinear L r c a ca c' a' ca' hc ha hca caMap).app U sc sa)
      ((Picard.PoincareBundle.Line.Fibers.pullBilinear L r b x bx b' x' bx' hb hx hbx bxMap).app U sb sx) :=
  Picard.PoincareBundle.Bilinear.InterchangeTransport.interchange
    (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback r.left (Picard.PoincareBundle.Line.Fibers.fiber_isLine L a) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L x) axMap)
    (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback r.left (Picard.PoincareBundle.Line.Fibers.fiber_isLine L b) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L x) bxMap)
    (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback r.left (Picard.PoincareBundle.Line.Fibers.fiber_isLine L c) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L b) cbMap)
    (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback r.left (Picard.PoincareBundle.Line.Fibers.fiber_isLine L c) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L a) caMap)
    (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback r.left (Picard.PoincareBundle.Line.Fibers.fiber_isLine L cb) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L ax) byMap)
    (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback r.left (Picard.PoincareBundle.Line.Fibers.fiber_isLine L ca) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L bx) azMap)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L r c c' hc) (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L r a a' ha)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L r b b' hb) (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L r x x' hx)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L r ca ca' hca) (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L r cb cb' hcb)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L r ax ax' hax) (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L r bx bx' hbx) (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L r w w' hw)
    (InterchangePullback.Construction.lineBilinear_interchange_pullback r.left (Picard.PoincareBundle.Line.Fibers.fiber_isLine L c) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L a)
      (Picard.PoincareBundle.Line.Fibers.fiber_isLine L b) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L x) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L ca) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L cb)
      (Picard.PoincareBundle.Line.Fibers.fiber_isLine L ax) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L bx) axMap bxMap cbMap caMap byMap azMap h) U sc sa sb sx

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberInterchangePullback.Construction
