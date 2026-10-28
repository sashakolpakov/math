import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCoordinateForms
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineFormsHomExt
import OAI.NumberTheory.PadicHodge.GeometricComparison.LocalizingPresheafSheafification

/-! # First Three Sheaf -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.FirstThreeSheaf.IntegralAffineFirstThreeSheaf

noncomputable section

/-! The first three native integral form sheaves on an affine scheme are associated module sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R A : Type) [CommRing R] [CommRing A] [Algebra R A]

def iso (n : ℕ) (hn : n ≤ 2) :
    (presheafToSheaf (Opens.grothendieckTopology (Spec (CommRingCat.of A))) (ModuleCat R)).obj
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) n) ≅
      (sheafCompose (Opens.grothendieckTopology (Spec (CommRingCat.of A)))
        (ModuleCat.restrictScalars (algebraMap R A))).obj
          (LocalizingPresheafSheaf.LocalizingPresheafBasis.associatedSheaf (CommRingCat.of A)
            (Affine.FormsCech.CoordinateForms.specPresheaf R A n)) :=
  (presheafToSheaf (Opens.grothendieckTopology (Spec (CommRingCat.of A))) (ModuleCat R)).mapIso
      (Intrinsic.AffineFormsHomExt.AffineCoordinates.nativeFormsPresheafIso R A n) ≪≫
    LocalizingPresheafSheafification.LocalizingPresheafBasis.sheafIsoComp (CommRingCat.of A)
      (Affine.FormsCech.CoordinateForms.specPresheaf R A n)
      (IntegralFirst.ThreeCoordinateForms.IntegralFirstThreeCoordinateForms.specPresheaf_isLocalized R A n hn)
      (ModuleCat.restrictScalars (algebraMap R A))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.FirstThreeSheaf.IntegralAffineFirstThreeSheaf
