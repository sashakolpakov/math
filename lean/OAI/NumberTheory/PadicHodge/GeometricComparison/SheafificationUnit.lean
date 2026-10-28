import Mathlib.CategoryTheory.Sites.Sheafification

/-! # Sheafification Unit -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SheafificationUnit.SheafificationUnitTransfer

noncomputable section

/-! Invertibility of the canonical sheafification map on an object is preserved by an actual presheaf isomorphism. -/

open _root_.CategoryTheory

universe u v u' v'

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {D : Type u'} [Category.{v'} D] [HasWeakSheafify J D]
  {P Q : Cᵒᵖ ⥤ D} (e : P ≅ Q) (U : Cᵒᵖ)

include e in
theorem of_iso (h : IsIso ((toSheafify J Q).app U)) : IsIso ((toSheafify J P).app U) := by
  have : IsIso (e.hom.app U) := (e.app U).isIso_hom
  have : IsIso ((sheafifyMap J e.hom).app U) :=
    (((sheafToPresheaf J D).mapIso ((presheafToSheaf J D).mapIso e)).app U).isIso_hom
  have ht : e.hom.app U ≫ (toSheafify J Q).app U =
      (toSheafify J P).app U ≫ (sheafifyMap J e.hom).app U :=
    congrArg (fun α => α.app U) (toSheafify_naturality J e.hom)
  have hi : IsIso ((toSheafify J P).app U ≫ (sheafifyMap J e.hom).app U) :=
    ht ▸ inferInstance
  exact (isIso_comp_right_iff _ _).mp hi

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SheafificationUnit.SheafificationUnitTransfer
