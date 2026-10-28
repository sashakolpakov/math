import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InterchangeOrigin
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.InterchangeTransport
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberBilinearRigidity

/-! # Fiber Interchange Origin -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberInterchangeOrigin.Construction

noncomputable section

/-! Interchange of actual line-fiber products is detected at the
origin of a proper smooth connected group parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback

universe u

theorem fiberBilinear_interchange_of_origin {k : Type u} [Field k]
    (T : Over (Spec (.of k))) [GrpObj T] [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]
    {E : Over (Spec (.of k))} (L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left)
    (c a b x ca cb ax bx w : T ⟶ E) (c' a' b' x' ca' cb' ax' bx' w' : 𝟙_ (Over (Spec (.of k))) ⟶ E)
    (hc : η[T] ≫ c = c') (ha : η[T] ≫ a = a') (hb : η[T] ≫ b = b') (hx : η[T] ≫ x = x')
    (hca : η[T] ≫ ca = ca') (hcb : η[T] ≫ cb = cb')
    (hax : η[T] ≫ ax = ax') (hbx : η[T] ≫ bx = bx') (hw : η[T] ≫ w = w')
    (axMap : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L a) (Picard.PoincareBundle.Line.Fibers.fiber L x) (Picard.PoincareBundle.Line.Fibers.fiber L ax))
    (bxMap : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L b) (Picard.PoincareBundle.Line.Fibers.fiber L x) (Picard.PoincareBundle.Line.Fibers.fiber L bx))
    (cbMap : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L c) (Picard.PoincareBundle.Line.Fibers.fiber L b) (Picard.PoincareBundle.Line.Fibers.fiber L cb))
    (caMap : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L c) (Picard.PoincareBundle.Line.Fibers.fiber L a) (Picard.PoincareBundle.Line.Fibers.fiber L ca))
    (byMap : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L cb) (Picard.PoincareBundle.Line.Fibers.fiber L ax) (Picard.PoincareBundle.Line.Fibers.fiber L w))
    (azMap : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L ca) (Picard.PoincareBundle.Line.Fibers.fiber L bx) (Picard.PoincareBundle.Line.Fibers.fiber L w))
    [hcaIso : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom caMap)] [hbxIso : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom bxMap)] [hazIso : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom azMap)]
    (h : ∀ (U : (𝟙_ (Over (Spec (.of k)))).left.Opens)
      (sc : Γ(Picard.PoincareBundle.Line.Fibers.fiber L c', U)) (sa : Γ(Picard.PoincareBundle.Line.Fibers.fiber L a', U)) (sb : Γ(Picard.PoincareBundle.Line.Fibers.fiber L b', U)) (sx : Γ(Picard.PoincareBundle.Line.Fibers.fiber L x', U)),
      (Picard.PoincareBundle.Line.Fibers.pullBilinear L η[T] cb ax w cb' ax' w' hcb hax hw byMap).app U
        ((Picard.PoincareBundle.Line.Fibers.pullBilinear L η[T] c b cb c' b' cb' hc hb hcb cbMap).app U sc sb)
        ((Picard.PoincareBundle.Line.Fibers.pullBilinear L η[T] a x ax a' x' ax' ha hx hax axMap).app U sa sx) =
      (Picard.PoincareBundle.Line.Fibers.pullBilinear L η[T] ca bx w ca' bx' w' hca hbx hw azMap).app U
        ((Picard.PoincareBundle.Line.Fibers.pullBilinear L η[T] c a ca c' a' ca' hc ha hca caMap).app U sc sa)
        ((Picard.PoincareBundle.Line.Fibers.pullBilinear L η[T] b x bx b' x' bx' hb hx hbx bxMap).app U sb sx))
    (U : T.left.Opens) (sc : Γ(Picard.PoincareBundle.Line.Fibers.fiber L c, U)) (sa : Γ(Picard.PoincareBundle.Line.Fibers.fiber L a, U))
    (sb : Γ(Picard.PoincareBundle.Line.Fibers.fiber L b, U)) (sx : Γ(Picard.PoincareBundle.Line.Fibers.fiber L x, U)) :
    byMap.app U (cbMap.app U sc sb) (axMap.app U sa sx) = azMap.app U (caMap.app U sc sa) (bxMap.app U sb sx) := by
  have hp := InterchangeTransport.Construction.lineBilinear_interchange_of_transport
    (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback η[T].left (Picard.PoincareBundle.Line.Fibers.fiber_isLine L a) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L x) axMap)
    (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback η[T].left (Picard.PoincareBundle.Line.Fibers.fiber_isLine L b) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L x) bxMap)
    (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback η[T].left (Picard.PoincareBundle.Line.Fibers.fiber_isLine L c) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L b) cbMap)
    (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback η[T].left (Picard.PoincareBundle.Line.Fibers.fiber_isLine L c) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L a) caMap)
    (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback η[T].left (Picard.PoincareBundle.Line.Fibers.fiber_isLine L cb) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L ax) byMap)
    (Picard.PoincareBundle.Bilinear.BilinearPullback.pullback η[T].left (Picard.PoincareBundle.Line.Fibers.fiber_isLine L ca) (Picard.PoincareBundle.Line.Fibers.fiber_isLine L bx) azMap)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L η[T] c c' hc) (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L η[T] a a' ha)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L η[T] b b' hb) (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L η[T] x x' hx)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L η[T] ca ca' hca) (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L η[T] cb cb' hcb)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L η[T] ax ax' hax) (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L η[T] bx bx' hbx)
    (Picard.PoincareBundle.Line.Fibers.fiberPullbackIso L η[T] w w' hw) h
  exact @InterchangeOrigin.Construction.lineBilinear_interchange_of_origin k inferInstance T inferInstance inferInstance inferInstance inferInstance
    (FiberBilinearRigidity.Construction.nativeFiberLine L c) (FiberBilinearRigidity.Construction.nativeFiberLine L a) (FiberBilinearRigidity.Construction.nativeFiberLine L b) (FiberBilinearRigidity.Construction.nativeFiberLine L x)
    (FiberBilinearRigidity.Construction.nativeFiberLine L ca) (FiberBilinearRigidity.Construction.nativeFiberLine L cb) (FiberBilinearRigidity.Construction.nativeFiberLine L ax) (FiberBilinearRigidity.Construction.nativeFiberLine L bx) (Picard.PoincareBundle.Line.Fibers.fiber L w)
    axMap bxMap cbMap caMap byMap azMap hcaIso hbxIso hazIso hp U sc sa sb sx

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberInterchangeOrigin.Construction
