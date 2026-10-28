import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeLocalization
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.FormsCech

/-! # Three Coordinate Forms -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCoordinateForms.IntegralFirstThreeCoordinateForms

noncomputable section

/-! Degree-zero, degree-one and degree-two coordinate-form presheaves localize before rationalization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

attribute [local instance] RelativeFormsFunctor.CoordinateForms.coordinateAlgebra

theorem formMap_isLocalized {B C : CommAlgCat.{u} A}
    (T : Submonoid A) (f : B ⟶ C) [IsLocalizedModule T f.hom.toLinearMap]
    (n : ℕ) (hn : n ≤ 2) : IsLocalizedModule T (RelativeFormsFunctor.CoordinateForms.formMap R A f n) := by
  let := RelativeFormsFunctor.CoordinateForms.baseAlgebra R A B
  let := RelativeFormsFunctor.CoordinateForms.baseAlgebra R A C
  let : Algebra B C := f.hom.toRingHom.toAlgebra
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun a => (f.hom.commutes a).symm)
  let : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq
    (fun r => (f.hom.commutes (algebraMap R A r)).symm)
  have hf : (IsScalarTower.toAlgHom A B C).toLinearMap = f.hom.toLinearMap := by
    ext b
    rfl
  let : IsLocalization (Algebra.algebraMapSubmonoid B T) C :=
    isLocalizedModule_iff_isLocalization.mp (by rw [hf]; infer_instance)
  let : IsLocalizedModule (Algebra.algebraMapSubmonoid B T)
      (Forms.CoordinateLinearity.FormsBaseChange.coordinateFormMap R B C n) :=
    ThreeLocalization.IntegralFirstThreeLocalization.isLocalized R B C (Algebra.algebraMapSubmonoid B T) n hn
  have h := IsLocalizedModule.restrictScalars T (Forms.CoordinateLinearity.FormsBaseChange.coordinateFormMap R B C n)
  convert h using 1
  apply LinearMap.ext
  intro ω
  rfl

theorem specPresheaf_isLocalized (n : ℕ) (hn : n ≤ 2) (a : A) :
    IsLocalizedModule (Submonoid.powers a)
      ((Affine.FormsCech.CoordinateForms.specPresheaf R A n).map (PrimeSpectrum.basicOpen a).leTop.op).hom := by
  let f := Affine.CoordinateLocalization.AffineCoordinates.principalRestriction A a
  let : IsLocalizedModule (Submonoid.powers a) ((Affine.CoordinateLocalization.AffineCoordinates.algebras A).map f).hom.toLinearMap :=
    Affine.CoordinateLocalization.AffineCoordinates.principal_restriction_isLocalized A a
  exact formMap_isLocalized R A (Submonoid.powers a) ((Affine.CoordinateLocalization.AffineCoordinates.algebras A).map f) n hn

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCoordinateForms.IntegralFirstThreeCoordinateForms
