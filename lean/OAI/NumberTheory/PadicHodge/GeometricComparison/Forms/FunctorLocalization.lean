import OAI.NumberTheory.PadicHodge.GeometricComparison.RelativeFormsLocalization

/-! # Functor Localization -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.FunctorLocalization.CoordinateForms

noncomputable section

/-! Localization of an algebra-valued diagram gives localization of its relative-form diagram. -/

open _root_.CategoryTheory

universe u v

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Algebra ℚ A]
  {I : Type v} [Category I] (F : I ⥤ CommAlgCat.{u} A)
  (T : Submonoid A) {i j : I} (f : i ⟶ j) (n : ℕ)

theorem localization_of_functor (hf : IsLocalizedModule T (F.map f).hom.toLinearMap) :
    IsLocalizedModule T (((F ⋙ RelativeFormsFunctor.CoordinateForms.functor R A n).map f).hom) := by
  let : Algebra ℚ (F.obj i) := ((algebraMap A (F.obj i)).comp (algebraMap ℚ A)).toAlgebra
  let : Algebra ℚ (F.obj j) := ((algebraMap A (F.obj j)).comp (algebraMap ℚ A)).toAlgebra
  let := hf
  exact RelativeFormsLocalization.CoordinateForms.formMap_isLocalized R A T (F.map f) n

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.FunctorLocalization.CoordinateForms
