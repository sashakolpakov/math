import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.GroupProductsInterchange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.ProductOrigin
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FramedProductLaws

/-! # Group Interchange -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.GroupInterchange.Construction

noncomputable section

/-! The image horizontal and vertical products satisfy interchange on
proper smooth connected group parameters, by the common origin frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  {B : Over (Spec (.of k))} [GrpObj B] [IsCommMonObj B]
  [IsProper B.hom] [Smooth B.hom] [GeometricallyIntegral B.hom]
  [IsLocallyNoetherian B.left]
  (D : FormalGeometry.Completion.Rigidified.ProductLine.Construction.RigidifiedProductLine B B)
  (βv : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.inputLeft B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.inputRight B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Vertical.ProductParameters.outputPoint B B)))
  (hβv : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βv))
  (βh : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.inputLeft B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.inputRight B B))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) (Picard.PoincareBundle.Product.ParameterSchemes.outputPoint B B)))
  (hβh : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom βh))

variable {C : Over (Spec (.of k))} (q : B ⟶ C)
  (i : uliftYoneda.{u + 1}.obj C ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)
  (hfac : uliftYoneda.map q ≫ i = ProductPicard.SheafMap.Construction.productNativePicardSheafMap (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv)

variable [IsAffineHom (q ⊗ₘ 𝟙 B).left] [Flat (q ⊗ₘ 𝟙 B).left]
  [Surjective (q ⊗ₘ 𝟙 B).left] [IsLocallyNoetherian (C ⊗ B).left]
  [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]

variable [GrpObj C] [IsMonHom q]

variable [IsCommMonObj C] [IsProper C.hom] [Smooth C.hom] [GeometricallyConnected C.hom]
open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

variable {T : Over (Spec (.of k))} [GrpObj T]
  [Smooth T.hom] [IsProper T.hom] [GeometricallyConnected T.hom]
local notation "Q" => OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.rigidifiedProductPicardImageLine D βv hβv βh hβh q i hfac
local notation "L" => OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)

theorem picardImageGroupProducts_interchange
    (c a b x ca cb ax bx w : T ⟶ C ⊗ B)
    [IsMonHom c] [IsMonHom a] [IsMonHom b] [IsMonHom x] [IsMonHom ca]
    [IsMonHom cb] [IsMonHom ax] [IsMonHom bx] [IsMonHom w]
    (hax : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst C B) (snd C B) a x ax)
    (hbx : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd C B) (fst C B) b x bx)
    (hcb : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst C B) (snd C B) c b cb)
    (hca : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd C B) (fst C B) c a ca)
    (hby : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd C B) (fst C B) cb ax w)
    (haz : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst C B) (snd C B) ca bx w)
    (U : T.left.Opens) (sc : Γ(Picard.PoincareBundle.Line.Fibers.fiber (L) c, U))
    (sa : Γ(Picard.PoincareBundle.Line.Fibers.fiber (L) a, U)) (sb : Γ(Picard.PoincareBundle.Line.Fibers.fiber (L) b, U))
    (sx : Γ(Picard.PoincareBundle.Line.Fibers.fiber (L) x, U)) :
    (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac cb ax w hby).app U ((GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac c b cb hcb).app U sc sb)
      ((GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac a x ax hax).app U sa sx) =
    (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac ca bx w haz).app U ((GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac c a ca hca).app U sc sa)
      ((GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac b x bx hbx).app U sb sx) := by
  exact GroupProductsInterchange.Construction.groupProducts_interchange_of_common_origin T (L) c a b x ca cb ax bx w
    (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac a x ax hax)
    (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac b x bx hbx)
    (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac c b cb hcb)
    (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac c a ca hca)
    (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac cb ax w hby)
    (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac ca bx w haz)
    (RigidifiedPointFrames.Construction.rigidifiedProductZeroFrame Q _)
    (ProductOrigin.Construction.picardImageHorizontalProduct_fiber_origin D βv hβv βh hβh q i hfac a x ax hax)
    (ProductOrigin.Construction.picardImageVerticalProduct_fiber_origin D βv hβv βh hβh q i hfac b x bx hbx)
    (ProductOrigin.Construction.picardImageHorizontalProduct_fiber_origin D βv hβv βh hβh q i hfac c b cb hcb)
    (ProductOrigin.Construction.picardImageVerticalProduct_fiber_origin D βv hβv βh hβh q i hfac c a ca hca)
    (ProductOrigin.Construction.picardImageVerticalProduct_fiber_origin D βv hβv βh hβh q i hfac cb ax w hby)
    (ProductOrigin.Construction.picardImageHorizontalProduct_fiber_origin D βv hβv βh hβh q i hfac ca bx w haz)
    U sc sa sb sx

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.GroupInterchange.Construction
