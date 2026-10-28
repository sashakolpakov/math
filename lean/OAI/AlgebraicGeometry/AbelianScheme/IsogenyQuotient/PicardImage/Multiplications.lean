import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.HorizontalAssociativity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.VerticalAssociativity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.LeftUnitLaws
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.RightUnitLaws

/-! # Multiplications -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.Multiplications.Construction

noncomputable section

/-! Both PoincareBundle fiberwise multiplications on the actual image line, with
all unit, associativity, and naturality laws supplied by proofs. -/

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

def picardImageHorizontalMultiplication :
    Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (fst C B) (snd C B) (L) where
  product := GlobalProducts.Construction.picardImageHorizontalProduct D βv hβv βh hβh q i hfac
  product_isIso := GlobalProducts.Construction.picardImageHorizontalProduct_isIso D βv hβv βh hβh q i hfac
  unitFrame := UnitFrames.Construction.picardImageHorizontalUnitFrame D βv hβv βh hβh q i hfac
  unit_left := LeftUnitLaws.Construction.picardImageHorizontalProduct_unit_left D βv hβv βh hβh q i hfac
  unit_right := RightUnitLaws.Construction.picardImageHorizontalProduct_unit_right D βv hβv βh hβh q i hfac
  associative := HorizontalAssociativity.Construction.picardImageHorizontalProduct_associative D βv hβv βh hβh q i hfac
  product_natural := ProductNaturality.Construction.picardImageHorizontalProduct_natural D βv hβv βh hβh q i hfac
  unit_natural := UnitFrames.Construction.picardImageHorizontalUnitFrame_natural D βv hβv βh hβh q i hfac

omit [IsMonHom q] in
def picardImageVerticalMultiplication :
    Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (snd C B) (fst C B) (L) where
  product := GlobalProducts.Construction.picardImageVerticalProduct D βv hβv βh hβh q i hfac
  product_isIso := GlobalProducts.Construction.picardImageVerticalProduct_isIso D βv hβv βh hβh q i hfac
  unitFrame := UnitFrames.Construction.picardImageVerticalUnitFrame D βv hβv βh hβh q i hfac
  unit_left := LeftUnitLaws.Construction.picardImageVerticalProduct_unit_left D βv hβv βh hβh q i hfac
  unit_right := RightUnitLaws.Construction.picardImageVerticalProduct_unit_right D βv hβv βh hβh q i hfac
  associative := VerticalAssociativity.Construction.picardImageVerticalProduct_associative D βv hβv βh hβh q i hfac
  product_natural := ProductNaturality.Construction.picardImageVerticalProduct_natural D βv hβv βh hβh q i hfac
  unit_natural := UnitFrames.Construction.picardImageVerticalUnitFrame_natural D βv hβv βh hβh q i hfac

theorem picardImageMultiplications_unit_zero (T : Over (Spec (.of k))) :
    (picardImageHorizontalMultiplication D βv hβv βh hβh q i hfac).unitFrame
      (1 : T ⟶ C ⊗ B) (MonObj.one_comp (fst C B)) =
    (picardImageVerticalMultiplication D βv hβv βh hβh q i hfac).unitFrame
      (1 : T ⟶ C ⊗ B) (MonObj.one_comp (snd C B)) :=
  (UnitFrames.Construction.picardImageHorizontalUnitFrame_zero D βv hβv βh hβh q i hfac T).trans
    (UnitFrames.Construction.picardImageVerticalUnitFrame_zero D βv hβv βh hβh q i hfac T).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.Multiplications.Construction
