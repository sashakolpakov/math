import OAI.NumberTheory.PadicHodge.IntegralComparison.Free.PresentationSheafSections

/-! # Presentation Linear Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Free.PresentationLinearSections

noncomputable section

/-! The actual free-presentation section coordinates respect the original coefficient action. -/

open _root_.CategoryTheory Opposite

universe u v

variable {C : Type (max u v)} [Category.{v} C] {ι : Type v} (F : ι → C)
  (R : Type (max u v)) [CommRing R]

def presheaf (H : Cᵒᵖ ⥤ ModuleCat.{max u v} R) :
    (PresentationSections.presheaf F R ⟶ H) ≃ₗ[R] (∀ i, H.obj (op (F i))) :=
  { PresentationSections.homEquiv F R H with
    map_smul' := by intros; rfl }

variable (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{max u v} R)]

def sheaf (H : Sheaf J (ModuleCat.{max u v} R)) :
    (PresentationSheafSections.sheaf F R J ⟶ H) ≃ₗ[R] (∀ i, H.obj.obj (op (F i))) :=
  (LinearAdjunction.homLinearEquiv R (sheafificationAdjunction J (ModuleCat.{max u v} R))
    (PresentationSections.presheaf F R) H).trans (presheaf F R H.obj)

theorem sheaf_apply (H : Sheaf J (ModuleCat.{max u v} R))
    (a : PresentationSheafSections.sheaf F R J ⟶ H) :
    sheaf F R J H a = PresentationSheafSections.homEquiv F R J H a := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Free.PresentationLinearSections
