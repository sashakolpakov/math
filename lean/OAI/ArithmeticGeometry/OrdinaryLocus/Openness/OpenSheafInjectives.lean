import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SkyscraperRestriction
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Open Sheaf Injectives -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenSheafInjectives.Construction

noncomputable section

/-! Restriction to an open subspace preserves injective abelian sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe u

variable {X : TopCat.{u}} (U : Opens X)

theorem injective_openRestrictSkyscraper (x : X) (I : AddCommGrpCat.{u}) [Injective I] :
    Injective (U.sheafRestrict.obj ((AbelianSheafInjectives.Construction.abelianSheafSkyscraper X x).obj I)) := by
  by_cases hx : x ∈ U
  · exact Injective.of_iso (SkyscraperRestriction.Construction.openRestrictSkyscraperIso U x I hx).symm
      (AbelianSheafInjectives.Construction.injective_abelianSheafSkyscraper (TopCat.of U) ⟨x, hx⟩ I)
  · exact (SkyscraperRestriction.Construction.openRestrictSkyscraper_isZero U x I hx).injective

theorem injective_openRestrict (F : AbelianSheafInjectives.Construction.AbelianSheaves X) [Injective F] :
    Injective (U.sheafRestrict.obj F) := by
  have hI (x : X) : Injective
      (U.sheafRestrict.obj (AbelianSheafInjectives.Construction.abelianSheafInjectiveFamily X F x)) :=
    injective_openRestrictSkyscraper U x _
  have hprod : Injective (U.sheafRestrict.obj (∏ᶜ AbelianSheafInjectives.Construction.abelianSheafInjectiveFamily X F)) :=
    Injective.of_iso (PreservesProduct.iso U.sheafRestrict (AbelianSheafInjectives.Construction.abelianSheafInjectiveFamily X F)).symm
      inferInstance
  let r : Retract F (∏ᶜ AbelianSheafInjectives.Construction.abelianSheafInjectiveFamily X F) :=
    { i := AbelianSheafInjectives.Construction.abelianSheafToInjective X F
      r := Injective.factorThru (𝟙 F) (AbelianSheafInjectives.Construction.abelianSheafToInjective X F)
      retract := Injective.comp_factorThru _ _ }
  exact (r.map U.sheafRestrict).injective

theorem openRestrict_preservesInjectiveObjects :
    (U.sheafRestrict (C := AddCommGrpCat.{u})).PreservesInjectiveObjects where
  injective_obj h := @injective_openRestrict _ U _ h

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenSheafInjectives.Construction
