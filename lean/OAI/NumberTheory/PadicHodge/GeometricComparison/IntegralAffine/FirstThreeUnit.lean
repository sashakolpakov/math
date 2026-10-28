import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.FirstThreeSheaf
import OAI.NumberTheory.PadicHodge.GeometricComparison.LocalizingPresheafUnit
import OAI.NumberTheory.PadicHodge.GeometricComparison.SheafificationUnit

/-! # First Three Unit -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.FirstThreeUnit.IntegralAffineFirstThreeSheaf

noncomputable section

/-! The actual integral form-sheaf sections on principal affine opens equal the presheaf sections in degrees zero, one and two. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (R A : Type) [CommRing R] [CommRing A] [Algebra R A]

theorem unit_basicOpen_isIso (n : ℕ) (hn : n ≤ 2) (a : A) :
    IsIso ((toSheafify (Opens.grothendieckTopology (Spec (CommRingCat.of A)))
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) n)).app
        (op (PrimeSpectrum.basicOpen a))) := by
  have h := LocalizingPresheafUnit.LocalizingPresheafBasis.unit_comp_basicOpen_isIso (CommRingCat.of A)
    (Affine.FormsCech.CoordinateForms.specPresheaf R A n)
    (IntegralFirst.ThreeCoordinateForms.IntegralFirstThreeCoordinateForms.specPresheaf_isLocalized R A n hn)
    (ModuleCat.restrictScalars (algebraMap R A)) a
  exact SheafificationUnit.SheafificationUnitTransfer.of_iso
    (Opens.grothendieckTopology (Spec (CommRingCat.of A)))
    (Intrinsic.AffineFormsHomExt.AffineCoordinates.nativeFormsPresheafIso R A n) (op (PrimeSpectrum.basicOpen a)) h

theorem unit_top_isIso (n : ℕ) (hn : n ≤ 2) :
    IsIso ((toSheafify (Opens.grothendieckTopology (Spec (CommRingCat.of A)))
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) n)).app (op ⊤)) := by
  have h : (PrimeSpectrum.basicOpen (1 : A) : (Spec (CommRingCat.of A)).Opens) = ⊤ :=
    PrimeSpectrum.basicOpen_one
  exact h ▸ unit_basicOpen_isIso R A n hn 1

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.FirstThreeUnit.IntegralAffineFirstThreeSheaf
