import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FiberInterchangeOrigin
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FramedProductLaws
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.NormalizedProductOrigin

/-! # Group Products Interchange -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GroupProductsInterchange.Construction

noncomputable section

/-! Products normalized in a common origin frame satisfy interchange
on proper smooth connected group parameters. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.BilinearPullback

universe u
variable {k : Type u} [Field k]
  (T : Over (Spec (.of k))) [GrpObj T]
  [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]
  {E : Over (Spec (.of k))} [GrpObj E] (L : Picard.PoincareBundle.Line.Bundles.LineBundle E.left)
  (c a b x ca cb ax bx w : T ⟶ E)
  [IsMonHom c] [IsMonHom a] [IsMonHom b] [IsMonHom x] [IsMonHom ca]
  [IsMonHom cb] [IsMonHom ax] [IsMonHom bx] [IsMonHom w]
  (axMap : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L a) (Picard.PoincareBundle.Line.Fibers.fiber L x) (Picard.PoincareBundle.Line.Fibers.fiber L ax))
  (bxMap : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L b) (Picard.PoincareBundle.Line.Fibers.fiber L x) (Picard.PoincareBundle.Line.Fibers.fiber L bx))
  (cbMap : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L c) (Picard.PoincareBundle.Line.Fibers.fiber L b) (Picard.PoincareBundle.Line.Fibers.fiber L cb))
  (caMap : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L c) (Picard.PoincareBundle.Line.Fibers.fiber L a) (Picard.PoincareBundle.Line.Fibers.fiber L ca))
  (byMap : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L cb) (Picard.PoincareBundle.Line.Fibers.fiber L ax) (Picard.PoincareBundle.Line.Fibers.fiber L w))
  (azMap : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (Picard.PoincareBundle.Line.Fibers.fiber L ca) (Picard.PoincareBundle.Line.Fibers.fiber L bx) (Picard.PoincareBundle.Line.Fibers.fiber L w))
  [IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom caMap)] [IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom bxMap)] [IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom azMap)]
  (z : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (𝟙_ (Over (Spec (.of k)))).left ≅
    Picard.PoincareBundle.Line.Fibers.fiber L (1 : 𝟙_ (Over (Spec (.of k))) ⟶ E))
  (hax : Picard.PoincareBundle.Line.Fibers.pullBilinear L η[T] a x ax 1 1 1
    (NormalizedProductOrigin.Construction.groupMap_origin a) (NormalizedProductOrigin.Construction.groupMap_origin x) (NormalizedProductOrigin.Construction.groupMap_origin ax) axMap = Poincare.BilinearProducts.Construction.framedLineProduct z z z)
  (hbx : Picard.PoincareBundle.Line.Fibers.pullBilinear L η[T] b x bx 1 1 1
    (NormalizedProductOrigin.Construction.groupMap_origin b) (NormalizedProductOrigin.Construction.groupMap_origin x) (NormalizedProductOrigin.Construction.groupMap_origin bx) bxMap = Poincare.BilinearProducts.Construction.framedLineProduct z z z)
  (hcb : Picard.PoincareBundle.Line.Fibers.pullBilinear L η[T] c b cb 1 1 1
    (NormalizedProductOrigin.Construction.groupMap_origin c) (NormalizedProductOrigin.Construction.groupMap_origin b) (NormalizedProductOrigin.Construction.groupMap_origin cb) cbMap = Poincare.BilinearProducts.Construction.framedLineProduct z z z)
  (hca : Picard.PoincareBundle.Line.Fibers.pullBilinear L η[T] c a ca 1 1 1
    (NormalizedProductOrigin.Construction.groupMap_origin c) (NormalizedProductOrigin.Construction.groupMap_origin a) (NormalizedProductOrigin.Construction.groupMap_origin ca) caMap = Poincare.BilinearProducts.Construction.framedLineProduct z z z)
  (hby : Picard.PoincareBundle.Line.Fibers.pullBilinear L η[T] cb ax w 1 1 1
    (NormalizedProductOrigin.Construction.groupMap_origin cb) (NormalizedProductOrigin.Construction.groupMap_origin ax) (NormalizedProductOrigin.Construction.groupMap_origin w) byMap = Poincare.BilinearProducts.Construction.framedLineProduct z z z)
  (haz : Picard.PoincareBundle.Line.Fibers.pullBilinear L η[T] ca bx w 1 1 1
    (NormalizedProductOrigin.Construction.groupMap_origin ca) (NormalizedProductOrigin.Construction.groupMap_origin bx) (NormalizedProductOrigin.Construction.groupMap_origin w) azMap = Poincare.BilinearProducts.Construction.framedLineProduct z z z)

include hax hbx hcb hca hby haz in
theorem groupProducts_interchange_of_common_origin
    (U : T.left.Opens) (sc : Γ(Picard.PoincareBundle.Line.Fibers.fiber L c, U)) (sa : Γ(Picard.PoincareBundle.Line.Fibers.fiber L a, U))
    (sb : Γ(Picard.PoincareBundle.Line.Fibers.fiber L b, U)) (sx : Γ(Picard.PoincareBundle.Line.Fibers.fiber L x, U)) :
    byMap.app U (cbMap.app U sc sb) (axMap.app U sa sx) =
      azMap.app U (caMap.app U sc sa) (bxMap.app U sb sx) := by
  apply FiberInterchangeOrigin.Construction.fiberBilinear_interchange_of_origin T L c a b x ca cb ax bx w 1 1 1 1 1 1 1 1 1
    (NormalizedProductOrigin.Construction.groupMap_origin c) (NormalizedProductOrigin.Construction.groupMap_origin a) (NormalizedProductOrigin.Construction.groupMap_origin b) (NormalizedProductOrigin.Construction.groupMap_origin x)
    (NormalizedProductOrigin.Construction.groupMap_origin ca) (NormalizedProductOrigin.Construction.groupMap_origin cb) (NormalizedProductOrigin.Construction.groupMap_origin ax) (NormalizedProductOrigin.Construction.groupMap_origin bx) (NormalizedProductOrigin.Construction.groupMap_origin w)
    axMap bxMap cbMap caMap byMap azMap _ U sc sa sb sx
  intro V c a b x
  rw [hax, hbx, hcb, hca, hby, haz]
  exact FramedProductLaws.Construction.framedLineProduct_interchange z z z z z z z z z V c a b x

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GroupProductsInterchange.Construction
