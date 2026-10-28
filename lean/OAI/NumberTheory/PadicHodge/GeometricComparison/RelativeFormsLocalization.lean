import OAI.NumberTheory.PadicHodge.GeometricComparison.RelativeFormsFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.Localization

/-! # Relative Forms Localization -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.RelativeFormsLocalization.CoordinateForms

noncomputable section

/-! Localizing a coordinate-algebra map localizes the corresponding relative-form presheaf map over the fixed affine base. -/

open _root_.CategoryTheory

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  {B C : CommAlgCat.{u} A} [Algebra ℚ B] [Algebra ℚ C]
  (T : Submonoid A) (f : B ⟶ C) [IsLocalizedModule T f.hom.toLinearMap]

attribute [local instance] RelativeFormsFunctor.CoordinateForms.coordinateAlgebra

theorem formMap_isLocalized (n : ℕ) : IsLocalizedModule T (RelativeFormsFunctor.CoordinateForms.formMap R A f n) := by
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
    Forms.Localization.FormsBaseChange.coordinateFormMap_isLocalized R B C (Algebra.algebraMapSubmonoid B T) n
  have h := IsLocalizedModule.restrictScalars T (Forms.CoordinateLinearity.FormsBaseChange.coordinateFormMap R B C n)
  convert h using 1
  apply LinearMap.ext
  intro ω
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.RelativeFormsLocalization.CoordinateForms
