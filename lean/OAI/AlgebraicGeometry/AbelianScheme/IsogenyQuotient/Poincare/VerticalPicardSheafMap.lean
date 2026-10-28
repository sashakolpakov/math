import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.PicardLocalSurjectivity
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.ProductParameters
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames

/-! # Vertical Picard Sheaf Map -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.VerticalPicardSheafMap.Construction

noncomputable section

/-! The vertical Poincare product defines a native Picard sheaf map.
An fppf parameter map to the original dual makes this map locally surjective. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FirstBiextensionFactor OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TransverseFrames OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

universe u
variable {S : Scheme.{u}} {A Z : Over S} [GrpObj A] [GrpObj Z]
  (φ : A ⟶ Z) [IsMonHom φ] (P : Picard.PoincareBundle.Line.Bundles.LineBundle (Z ⊗ A).left)
  (Dv : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (snd Z A) (fst Z A) P)

def poincareVerticalPicardSheafMap :
    uliftYoneda.{u + 1}.obj A ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf A).obj :=
  ProductPicard.SheafMap.Construction.productNativePicardSheafMap (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P φ)
    (Picard.PoincareBundle.Vertical.ProductParameters.globalProduct A A (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P φ) (Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical φ P Dv))
    (Picard.PoincareBundle.Vertical.ProductParameters.globalProduct_isIso A A (Picard.PoincareBundle.FirstBiextensionFactor.familyLine P φ) (Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical φ P Dv))

variable (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (ell : A ⟶ D.abelian)
  (DvD : Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (snd D.abelian A) (fst D.abelian A) (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.poincare))

include DvD in
theorem poincareVerticalPicardSheafMap_locallySurjective
    [Flat ell.left] [Surjective ell.left] [LocallyOfFinitePresentation ell.left] :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (poincareVerticalPicardSheafMap ell (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.poincare) DvD) :=
  PicardLocalSurjectivity.Construction.poincareFamily_nativePicard_locallySurjective D ell
    (Picard.PoincareBundle.Vertical.ProductParameters.globalProduct A A _ (Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical ell _ DvD))
    (Picard.PoincareBundle.Vertical.ProductParameters.globalProduct_isIso A A _ (Picard.PoincareBundle.Poincare.TransverseFrames.sourceVertical ell _ DvD))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.VerticalPicardSheafMap.Construction
