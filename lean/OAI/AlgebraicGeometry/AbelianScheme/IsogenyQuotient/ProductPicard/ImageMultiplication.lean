import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageLineValue
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageGroup
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RigidifiedProductClassMultiplication

/-! # Image Multiplication -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageMultiplication.Construction

noncomputable section

/-! The descended Picard image line is multiplicative in its image
parameter. Both its relative values and its actual line classes follow
from the original Picard homomorphism and the derived quotient embedding. -/

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
  (hfac : uliftYoneda.map q ≫ i = SheafMap.Construction.productNativePicardSheafMap (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv)

variable [IsAffineHom (q ⊗ₘ 𝟙 B).left] [Flat (q ⊗ₘ 𝟙 B).left]
  [Surjective (q ⊗ₘ 𝟙 B).left] [IsLocallyNoetherian (C ⊗ B).left]
  [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]

variable [GrpObj C] [IsMonHom q]

set_option backward.isDefEq.respectTransparency false in
theorem normalizedProductPicardImageLine_relative_mul {T : Over (Spec (.of k))} (x y : T ⟶ C) :
    (ImageLine.Construction.rigidifiedProductPicardImageLine D βv hβv βh hβh q i hfac).relativeValue (x * y) =
      (ImageLine.Construction.rigidifiedProductPicardImageLine D βv hβv βh hβh q i hfac).relativeValue x *
        (ImageLine.Construction.rigidifiedProductPicardImageLine D βv hβv βh hβh q i hfac).relativeValue y := by
  rw [ImageLineValue.Construction.normalizedProductPicardImageLine_family_value, ImageLineValue.Construction.normalizedProductPicardImageLine_family_value,
    ImageLineValue.Construction.normalizedProductPicardImageLine_family_value, ImageGroup.Construction.productPicardImage_mul (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.bundle) βv hβv βh hβh q i hfac]
  rw [← Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardSheafInclusionHom_apply, ← Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardSheafInclusionHom_apply,
    ← Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardSheafInclusionHom_apply, map_mul]

set_option backward.isDefEq.respectTransparency false in
theorem normalizedProductPicardImageLine_class_mul {T : Over (Spec (.of k))}
    [IsLocallyNoetherian T.left] (x y : T ⟶ C) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((ImageLine.Construction.rigidifiedProductPicardImageLine D βv hβv βh hβh q i hfac).line (x * y)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((ImageLine.Construction.rigidifiedProductPicardImageLine D βv hβv βh hβh q i hfac).line x) *
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((ImageLine.Construction.rigidifiedProductPicardImageLine D βv hβv βh hβh q i hfac).line y) :=
  RigidifiedProductClassMultiplication.Construction.rigidifiedProductLine_class_mul (ImageLine.Construction.rigidifiedProductPicardImageLine D βv hβv βh hβh q i hfac) x y
    (normalizedProductPicardImageLine_relative_mul D βv hβv βh hβh q i hfac x y)

def productPicardImageTensorIso {T : Over (Spec (.of k))} [IsLocallyNoetherian T.left] (x y : T ⟶ C) :
    AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule ((ImageLine.Construction.rigidifiedProductPicardImageLine D βv hβv βh hβh q i hfac).line x).sheaf
        ((ImageLine.Construction.rigidifiedProductPicardImageLine D βv hβv βh hβh q i hfac).line y).sheaf ≅
      ((ImageLine.Construction.rigidifiedProductPicardImageLine D βv hβv βh hβh q i hfac).line (x * y)).sheaf :=
  Classical.choice (Quotient.exact
    (normalizedProductPicardImageLine_class_mul D βv hβv βh hβh q i hfac x y).symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.ImageMultiplication.Construction
