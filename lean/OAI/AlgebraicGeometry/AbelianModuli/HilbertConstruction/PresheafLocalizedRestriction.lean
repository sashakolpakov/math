import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Module.LocalizedModule.Basic

/-! # Presheaf Localized Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresheafLocalizedRestriction

noncomputable section

/-! A natural tensor-comparison map transports localization to ordinary section restrictions. -/

open _root_.CategoryTheory

universe u v w

variable {R : Type u} [CommRing R] {C : Type v} [Category.{w} C]

theorem presheafRestriction_isLocalized_of_comparison
    (S : Submonoid R) {F G : C ⥤ ModuleCat.{u} R} (η : F ⟶ G)
    {U V : C} (i : U ⟶ V) [IsIso (η.app V)] [IsIso (G.map i)]
    [IsLocalizedModule S (η.app U).hom] : IsLocalizedModule S (F.map i).hom := by
  let e : G.obj U ≅ F.obj V := asIso (G.map i) ≪≫ (asIso (η.app V)).symm
  have he : η.app U ≫ e.hom = F.map i := by
    change η.app U ≫ G.map i ≫ inv (η.app V) = F.map i
    rw [← Category.assoc, ← η.naturality i, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hlinear : e.toLinearEquiv.toLinearMap.comp (η.app U).hom = (F.map i).hom :=
    congrArg ModuleCat.Hom.hom he
  have h := IsLocalizedModule.of_linearEquiv S (η.app U).hom e.toLinearEquiv
  rw [hlinear] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresheafLocalizedRestriction
