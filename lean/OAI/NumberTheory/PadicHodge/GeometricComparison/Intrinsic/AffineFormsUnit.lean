import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineFormsSheaf
import OAI.NumberTheory.PadicHodge.GeometricComparison.LocalizingPresheafUnit
import OAI.NumberTheory.PadicHodge.GeometricComparison.SheafificationUnit

/-! # Affine Forms Unit -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineFormsUnit.AffineCoordinates

noncomputable section

/-! The canonical native form-presheaf map to its sheafification is invertible on principal opens, including the whole affine spectrum. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra ℚ A]

theorem nativeForms_unit_basicOpen_isIso (n : ℕ) (a : A) :
    IsIso ((toSheafify (Opens.grothendieckTopology (Spec (CommRingCat.of A)))
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) n)).app (op (PrimeSpectrum.basicOpen a))) := by
  have h := LocalizingPresheafUnit.LocalizingPresheafBasis.unit_comp_basicOpen_isIso (CommRingCat.of A)
    (Affine.FormsCech.CoordinateForms.specPresheaf R A n) (Affine.FormsCech.CoordinateForms.specPresheaf_isLocalized R A n)
    (ModuleCat.restrictScalars (algebraMap R A)) a
  exact SheafificationUnit.SheafificationUnitTransfer.of_iso
    (Opens.grothendieckTopology (Spec (CommRingCat.of A)))
    (AffineFormsHomExt.AffineCoordinates.nativeFormsPresheafIso R A n) (op (PrimeSpectrum.basicOpen a)) h

theorem nativeForms_unit_top_isIso (n : ℕ) :
    IsIso ((toSheafify (Opens.grothendieckTopology (Spec (CommRingCat.of A)))
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) n)).app (op ⊤)) := by
  have h : (PrimeSpectrum.basicOpen (1 : A) : (Spec (CommRingCat.of A)).Opens) = ⊤ :=
    PrimeSpectrum.basicOpen_one
  exact h ▸ nativeForms_unit_basicOpen_isIso R A n 1

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineFormsUnit.AffineCoordinates
