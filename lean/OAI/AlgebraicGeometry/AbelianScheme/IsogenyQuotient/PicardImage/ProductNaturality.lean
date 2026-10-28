import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.GlobalProducts

/-! # Product Naturality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.ProductNaturality.Construction

noncomputable section

/-! The actual universal image products commute with every geometric
pullback of test schemes. -/

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

local notation "L" => OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)

theorem picardImageHorizontalProduct_natural {T U : Over (Spec (.of k))} (r : U ⟶ T)
    (a b c : T ⟶ C ⊗ B) (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst C B) (snd C B) a b c)
    (a' b' c' : U ⟶ C ⊗ B) (h' : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst C B) (snd C B) a' b' c')
    (ha : r ≫ a = a') (hb : r ≫ b = b') (hc : r ≫ c = c') :
    Picard.PoincareBundle.Line.Fibers.pullBilinear L r a b c a' b' c' ha hb hc (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac a b c h) =
      GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac a' b' c' h' :=
  Universal.LineProducts.Construction.lineProductFromUniversal_natural _ _ r a b c h a' b' c' h' ha hb hc

omit [IsMonHom q] [IsCommMonObj C] in
theorem picardImageVerticalProduct_natural {T U : Over (Spec (.of k))} (r : U ⟶ T)
    (a b c : T ⟶ C ⊗ B) (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd C B) (fst C B) a b c)
    (a' b' c' : U ⟶ C ⊗ B) (h' : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd C B) (fst C B) a' b' c')
    (ha : r ≫ a = a') (hb : r ≫ b = b') (hc : r ≫ c = c') :
    Picard.PoincareBundle.Line.Fibers.pullBilinear L r a b c a' b' c' ha hb hc (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac a b c h) =
      GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac a' b' c' h' :=
  Universal.VerticalProducts.Construction.verticalProductFromUniversal_natural _ _ r a b c h a' b' c' h' ha hb hc

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.ProductNaturality.Construction
