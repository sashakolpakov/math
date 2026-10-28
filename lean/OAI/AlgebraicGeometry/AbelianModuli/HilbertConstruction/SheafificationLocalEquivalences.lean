/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Localization.Monoidal.Basic

/-! # Sheafification Local Equivalences -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SheafificationLocalEquivalences.SheafTensorLocalization

noncomputable section

/-! The module-sheafification localization is exactly local bijectivity. -/

universe v v' u u'

open _root_.CategoryTheory MonoidalCategory _root_.PresheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}] [HasWeakSheafify J AddCommGrpCat.{v}]

/-- The class of morphisms of presheaves of modules inverted by the sheafification
functor: the localizing class for `SheafOfModules`. -/
def sheafificationW : MorphismProperty (PresheafOfModules.{v} R₀) :=
  (MorphismProperty.isomorphisms _).inverseImage (sheafification.{v} α)

lemma sheafificationW_iff {M N : PresheafOfModules.{v} R₀} (f : M ⟶ N) :
    sheafificationW.{v} α f ↔ IsIso ((sheafification.{v} α).map f) :=
  Iff.rfl

/-- Membership in the localizing class is local bijectivity of the underlying morphism
of presheaves of abelian groups: the sheafification of modules inverts exactly the
locally bijective maps. -/
lemma sheafificationW_iff_isLocallyBijective {M N : PresheafOfModules.{v} R₀}
    (f : M ⟶ N) :
    sheafificationW.{v} α f ↔
      Presheaf.IsLocallyInjective J ((toPresheaf R₀).map f) ∧
        Presheaf.IsLocallySurjective J ((toPresheaf R₀).map f) := by
  rw [sheafificationW_iff]
  constructor
  · intro h
    have h1 : IsIso ((SheafOfModules.toSheaf R).map ((sheafification.{v} α).map f)) :=
      inferInstance
    have h2 : IsIso ((presheafToSheaf J AddCommGrpCat).map ((toPresheaf R₀).map f)) := h1
    have h3 : J.W ((toPresheaf R₀).map f) := (J.W_iff _).mpr h2
    exact ⟨h3.isLocallyInjective, h3.isLocallySurjective⟩
  · rintro ⟨h1, h2⟩
    have h3 : J.W ((toPresheaf R₀).map f) := J.W_of_isLocallyBijective _
    have h4 : IsIso ((presheafToSheaf J AddCommGrpCat).map ((toPresheaf R₀).map f)) :=
      (J.W_iff _).mp h3
    have h5 : IsIso ((SheafOfModules.toSheaf R).map ((sheafification.{v} α).map f)) := h4
    exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf R)

variable (R' : Sheaf J RingCat.{u})

/-- At `α = 𝟙` the sheafification adjunction is reflective (`forget` is fully faithful
and `restrictScalars (𝟙 _)` is an equivalence), so the sheafification functor is a
localization at `sheafificationW`. -/
instance sheafificationW_isLocalization :
    (sheafification.{v} (𝟙 R'.obj)).IsLocalization (sheafificationW.{v} (𝟙 R'.obj)) := by
  have h : ((SheafOfModules.forget R' ⋙ restrictScalars (𝟙 R'.obj))).Full :=
    Functor.Full.comp _ _
  have h' : ((SheafOfModules.forget R' ⋙ restrictScalars (𝟙 R'.obj))).Faithful :=
    Functor.Faithful.comp _ _
  exact (sheafificationAdjunction (𝟙 R'.obj)).isLocalization

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SheafificationLocalEquivalences.SheafTensorLocalization
