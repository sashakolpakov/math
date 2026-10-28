import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineFormsHomExt
import OAI.NumberTheory.PadicHodge.GeometricComparison.LocalizingPresheafSheafification

/-! # Affine Forms Sheaf -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineFormsSheaf.AffineCoordinates

noncomputable section

/-! The native sheafified relative forms on an affine spectrum are the actual associated coordinate-module sheaf with restricted base scalars. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra ℚ A]

def nativeFormsSheafIso (n : ℕ) :
    (presheafToSheaf (Opens.grothendieckTopology (Spec (CommRingCat.of A))) (ModuleCat R)).obj
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) n) ≅
      (sheafCompose (Opens.grothendieckTopology (Spec (CommRingCat.of A)))
        (ModuleCat.restrictScalars (algebraMap R A))).obj
          (LocalizingPresheafSheaf.LocalizingPresheafBasis.associatedSheaf (CommRingCat.of A)
            (Affine.FormsCech.CoordinateForms.specPresheaf R A n)) :=
  (presheafToSheaf (Opens.grothendieckTopology (Spec (CommRingCat.of A))) (ModuleCat R)).mapIso
      (AffineFormsHomExt.AffineCoordinates.nativeFormsPresheafIso R A n) ≪≫
    LocalizingPresheafSheafification.LocalizingPresheafBasis.sheafIsoComp (CommRingCat.of A)
      (Affine.FormsCech.CoordinateForms.specPresheaf R A n) (Affine.FormsCech.CoordinateForms.specPresheaf_isLocalized R A n)
      (ModuleCat.restrictScalars (algebraMap R A))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineFormsSheaf.AffineCoordinates
