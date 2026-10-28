import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineFormsSheaf
import OAI.NumberTheory.PadicHodge.GeometricComparison.AssociatedModule
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.CechSheaf

/-! # Affine Forms Cech Vanishing -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineFormsCechVanishing.AffineCoordinates

noncomputable section

/-! The actual sheafified native affine differential forms have vanishing positive Čech cohomology on every finite principal cover. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite

variable (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra ℚ A]
  {ι : Type} [Finite ι] (s : ι → A) (hs : Ideal.span (Set.range s) = ⊤)

include hs in
theorem nativeForms_cech_exactAt_succ (j n : ℕ) :
    ((Cech.CechSheaf.functor R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A)
      (fun i => PrimeSpectrum.basicOpen (s i))).obj
        ((presheafToSheaf (Opens.grothendieckTopology (Spec (CommRingCat.of A))) (ModuleCat R)).obj
          (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formsPresheaf R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A) j))).ExactAt (n + 1) := by
  have h := AssociatedModule.AssociatedModuleCech.comp_exactAt_succ (CommRingCat.of A)
    ((Affine.FormsCech.CoordinateForms.specPresheaf R A j).obj (op ⊤)) s hs
    (ModuleCat.restrictScalars (algebraMap R A)) n
  exact h.of_iso ((Cech.CechSheaf.functor R (RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A)
    (fun i => PrimeSpectrum.basicOpen (s i))).mapIso (AffineFormsSheaf.AffineCoordinates.nativeFormsSheafIso R A j).symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AffineFormsCechVanishing.AffineCoordinates
