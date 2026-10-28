import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ProductPicard.SheafMap
import OAI.AlgebraicGeometry.Picard.PoincareBundle.FamilyRecovery
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledPoincareDetection

/-! # Picard Sheaf Value -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.PicardSheafValue.Construction

noncomputable section

/-! The actual native Picard-sheaf value of a Poincare family agrees
with its original representing map. Only the source dual is used. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledPoincareDetection.Construction.UnbundledPicard

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A]
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (φ : B ⟶ D.abelian)
  (β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.poincare) φ)
      (Picard.PoincareBundle.Vertical.ProductParameters.inputLeft B A))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.poincare) φ)
      (Picard.PoincareBundle.Vertical.ProductParameters.inputRight B A))
    (Picard.PoincareBundle.Line.Fibers.fiber (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.poincare) φ)
      (Picard.PoincareBundle.Vertical.ProductParameters.outputPoint B A)))
  (hβ : IsIso (Picard.PoincareBundle.Bilinear.BilinearPullback.toHom β))

theorem poincareFamily_nativePicard_value {T : Over S} (x : T ⟶ B) :
    (ProductPicard.SheafMap.Construction.productNativePicardSheafMap (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.poincare) φ)
      β hβ).app (op T) (ULift.up x) = D.representable.homEquiv (x ≫ φ) := by
  have hmono : Mono ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion A).hom.app (op T)) := inferInstance
  apply (CategoryTheory.mono_iff_injective _).mp hmono
  rw [← Picard.Homomorphisms.UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass_eq_representation]
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (Picard.Homomorphisms.UnbundledPoincareDetection.Construction.UnbundledPicard.homogeneousPicardSheafInclusion_toSheafify A) (op T))
    (ProductPicard.SheafMap.Construction.productNativeHomogeneousClass
      (Picard.PoincareBundle.FirstBiextensionFactor.familyLine (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.poincare) φ) β hβ x)
  apply h.trans
  apply congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A).app (op T))
  exact congrArg (Picard.PoincareBundle.Line.Comparison.Bundle.classEquiv (T ⊗ A).left)
    (Picard.PoincareBundle.FamilyRecovery.Family.familyClass_familyLine (Picard.PoincareBundle.Line.Comparison.Bundle.fromShared D.poincare) φ x)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.PicardSheafValue.Construction
