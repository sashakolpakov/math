import Mathlib.CategoryTheory.Sites.Sheafification

/-! # Sheafification Unit Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SheafificationUnitIso

noncomputable section

/-! Invariance of the actual sheafification unit under an isomorphism of presheaves. -/

open _root_.CategoryTheory

universe u v w z

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
  (J : GrothendieckTopology C) [HasWeakSheafify J D]
  {P Q : Cᵒᵖ ⥤ D} (e : P ≅ Q) (U : Cᵒᵖ)

include e in
theorem of_iso [IsIso ((toSheafify J P).app U)] : IsIso ((toSheafify J Q).app U) := by
  have h := congrArg (fun f => f.app U) (toSheafify_naturality J e.hom)
  change e.hom.app U ≫ (toSheafify J Q).app U =
    (toSheafify J P).app U ≫ (sheafifyMap J e.hom).app U at h
  have : IsIso (e.hom.app U ≫ (toSheafify J Q).app U) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left (e.hom.app U) _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SheafificationUnitIso
