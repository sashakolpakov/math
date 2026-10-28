import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.CoordinateLocalization
import OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.FunctorLocalization
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.Cech

/-! # Forms Cech -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.FormsCech.CoordinateForms

noncomputable section

/-! The actual relative-form presheaf has an exact Čech augmentation on finite principal affine covers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Algebra ℚ A]

abbrev specPresheaf (n : ℕ) : (Spec (CommRingCat.of A)).Opensᵒᵖ ⥤ ModuleCat.{u} A :=
  CoordinateLocalization.AffineCoordinates.algebras A ⋙ RelativeFormsFunctor.CoordinateForms.functor R A n

theorem specPresheaf_isLocalized (n : ℕ) (a : A) :
    IsLocalizedModule (Submonoid.powers a)
      ((specPresheaf R A n).map (PrimeSpectrum.basicOpen a).leTop.op).hom := by
  exact @Forms.FunctorLocalization.CoordinateForms.localization_of_functor R A _ _ _ _ ((Spec (CommRingCat.of A)).Opensᵒᵖ)
    (@CategoryTheory.Category.opposite ((Spec (CommRingCat.of A)).Opens) inferInstance)
    (CoordinateLocalization.AffineCoordinates.algebras A) (Submonoid.powers a)
    (Opposite.op (⊤ : (Spec (CommRingCat.of A)).Opens))
    (Opposite.op (PrimeSpectrum.basicOpen a : (Spec (CommRingCat.of A)).Opens))
    (CoordinateLocalization.AffineCoordinates.principalRestriction A a) n
    (CoordinateLocalization.AffineCoordinates.principal_restriction_isLocalized A a)

theorem spec_cech_quasiIso {ι : Type u} [Finite ι] (s : ι → A)
    (hs : Ideal.span (Set.range s) = ⊤) (n : ℕ) :
    QuasiIso (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.augmentation A (AlgebraicGeometry.Crystalline.Cohomology.Affine.Cech.AffineCech.model A)
      (fun i => AlgebraicGeometry.Crystalline.Cohomology.Affine.IntersectionLocalization.AffineIntersectionLocalization.principal A (s i)) (specPresheaf R A n)) :=
  AlgebraicGeometry.Crystalline.Cohomology.Affine.Cech.AffineCech.quasiIso A s (specPresheaf R A n) (specPresheaf_isLocalized R A n) hs

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.FormsCech.CoordinateForms
