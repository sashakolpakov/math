import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.LeftUnitLaws
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.GroupRightUnits
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Product.RelationSwap

/-! # Right Unit Laws -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.RightUnitLaws.Construction

noncomputable section

/-! The image products satisfy their right unit laws on every test
scheme by pullback from the universal group unit configurations. -/

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

attribute [local instance] LeftUnitLaws.Construction.imageProductSpace_smooth LeftUnitLaws.Construction.imageProductSpace_proper LeftUnitLaws.Construction.imageProductSpace_connected
local notation "Q" => OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.rigidifiedProductPicardImageLine D βv hβv βh hβh q i hfac
local notation "L" => OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle.fromShared (OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLine.Construction.normalizedProductPicardImageLine D βv hβv βh hβh q i hfac)

theorem picardImageHorizontalRightUnit_end {T : Over (Spec (.of k))}
    (x a : T ⟶ (C ⊗ B)) (ha : a ≫ fst C B = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst C B) (snd C B) x a x) :
    RightContraction.Construction.lineContractRight (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac x a x h) (UnitFrames.Construction.picardImageHorizontalUnitFrame D βv hβv βh hβh q i hfac a ha).hom =
      𝟙 (Picard.PoincareBundle.Line.Fibers.fiber (L) x) := by
  have hf := Product.UnitParameters.Construction.productHorizontalUnitParameter_factor C B a x ha (Product.RelationSwap.Construction.productRel_swap h)
  have hu := GroupRightUnits.Construction.picardImageHorizontalGroupRightUnit_end D βv hβv βh hβh q i hfac (𝟙 ((C ⊗ B))) (Product.UnitParameters.Construction.productHorizontalUnitParameter C B)
    (Product.UnitParameters.Construction.productHorizontalUnitParameter_first C B) (Product.RelationSwap.Construction.productRel_swap (Product.UnitParameters.Construction.productHorizontalUnitParameter_relation C B))
  have hp := RightContraction.Construction.contractedRightUnit_pullback (L) x
    (𝟙 ((C ⊗ B))) (Product.UnitParameters.Construction.productHorizontalUnitParameter C B) x a (Category.comp_id x) hf
    (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac (𝟙 _) (Product.UnitParameters.Construction.productHorizontalUnitParameter C B) (𝟙 _)
      (Product.RelationSwap.Construction.productRel_swap (Product.UnitParameters.Construction.productHorizontalUnitParameter_relation C B)))
    (UnitFrames.Construction.picardImageHorizontalUnitFrame D βv hβv βh hβh q i hfac (Product.UnitParameters.Construction.productHorizontalUnitParameter C B) (Product.UnitParameters.Construction.productHorizontalUnitParameter_first C B)).hom hu
  rw [ProductNaturality.Construction.picardImageHorizontalProduct_natural D βv hβv βh hβh q i hfac x (𝟙 _) (Product.UnitParameters.Construction.productHorizontalUnitParameter C B) (𝟙 _)
      (Product.RelationSwap.Construction.productRel_swap (Product.UnitParameters.Construction.productHorizontalUnitParameter_relation C B)) x a x h (Category.comp_id x) hf (Category.comp_id x),
    UnitFrames.Construction.picardImageHorizontalUnitFrame_natural D βv hβv βh hβh q i hfac x (Product.UnitParameters.Construction.productHorizontalUnitParameter C B) a
      (Product.UnitParameters.Construction.productHorizontalUnitParameter_first C B) ha hf] at hp
  exact hp

theorem picardImageHorizontalProduct_unit_right {T : Over (Spec (.of k))}
    (x a : T ⟶ (C ⊗ B)) (ha : a ≫ fst C B = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst C B) (snd C B) x a x)
    (U : T.left.Opens) (m : Γ(Picard.PoincareBundle.Line.Fibers.fiber (L) x, U)) :
    (GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac x a x h).app U m
      ((UnitFrames.Construction.picardImageHorizontalUnitFrame D βv hβv βh hβh q i hfac a ha).hom.app U (1 : Γ(T.left, U))) = m :=
  (RightContraction.Construction.lineContractRight_app _ _ U m).symm.trans
    (congrArg (fun f => f.app U m) (picardImageHorizontalRightUnit_end D βv hβv βh hβh q i hfac x a ha h))

omit [IsMonHom q] in
theorem picardImageVerticalRightUnit_end {T : Over (Spec (.of k))}
    (x a : T ⟶ (C ⊗ B)) (ha : a ≫ snd C B = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd C B) (fst C B) x a x) :
    RightContraction.Construction.lineContractRight (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac x a x h) (UnitFrames.Construction.picardImageVerticalUnitFrame D βv hβv βh hβh q i hfac a ha).hom =
      𝟙 (Picard.PoincareBundle.Line.Fibers.fiber (L) x) := by
  have hf := Product.UnitParameters.Construction.productVerticalUnitParameter_factor C B a x ha (Product.RelationSwap.Construction.productRel_swap h)
  have hu := GroupRightUnits.Construction.picardImageVerticalGroupRightUnit_end D βv hβv βh hβh q i hfac (𝟙 ((C ⊗ B))) (Product.UnitParameters.Construction.productVerticalUnitParameter C B)
    (Product.UnitParameters.Construction.productVerticalUnitParameter_second C B) (Product.RelationSwap.Construction.productRel_swap (Product.UnitParameters.Construction.productVerticalUnitParameter_relation C B))
  have hp := RightContraction.Construction.contractedRightUnit_pullback (L) x
    (𝟙 ((C ⊗ B))) (Product.UnitParameters.Construction.productVerticalUnitParameter C B) x a (Category.comp_id x) hf
    (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac (𝟙 _) (Product.UnitParameters.Construction.productVerticalUnitParameter C B) (𝟙 _)
      (Product.RelationSwap.Construction.productRel_swap (Product.UnitParameters.Construction.productVerticalUnitParameter_relation C B)))
    (UnitFrames.Construction.picardImageVerticalUnitFrame D βv hβv βh hβh q i hfac (Product.UnitParameters.Construction.productVerticalUnitParameter C B) (Product.UnitParameters.Construction.productVerticalUnitParameter_second C B)).hom hu
  rw [ProductNaturality.Construction.picardImageVerticalProduct_natural D βv hβv βh hβh q i hfac x (𝟙 _) (Product.UnitParameters.Construction.productVerticalUnitParameter C B) (𝟙 _)
      (Product.RelationSwap.Construction.productRel_swap (Product.UnitParameters.Construction.productVerticalUnitParameter_relation C B)) x a x h (Category.comp_id x) hf (Category.comp_id x),
    UnitFrames.Construction.picardImageVerticalUnitFrame_natural D βv hβv βh hβh q i hfac x (Product.UnitParameters.Construction.productVerticalUnitParameter C B) a
      (Product.UnitParameters.Construction.productVerticalUnitParameter_second C B) ha hf] at hp
  exact hp

omit [IsMonHom q] in
theorem picardImageVerticalProduct_unit_right {T : Over (Spec (.of k))}
    (x a : T ⟶ (C ⊗ B)) (ha : a ≫ snd C B = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd C B) (fst C B) x a x)
    (U : T.left.Opens) (m : Γ(Picard.PoincareBundle.Line.Fibers.fiber (L) x, U)) :
    (GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac x a x h).app U m
      ((UnitFrames.Construction.picardImageVerticalUnitFrame D βv hβv βh hβh q i hfac a ha).hom.app U (1 : Γ(T.left, U))) = m :=
  (RightContraction.Construction.lineContractRight_app _ _ U m).symm.trans
    (congrArg (fun f => f.app U m) (picardImageVerticalRightUnit_end D βv hβv βh hβh q i hfac x a ha h))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.RightUnitLaws.Construction
