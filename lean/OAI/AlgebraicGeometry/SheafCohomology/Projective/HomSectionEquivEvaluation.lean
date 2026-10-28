import OAI.AlgebraicGeometry.SheafCohomology.Projective.UnitHomTopSections

/-! # Hom Section Equiv Evaluation -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.HomSectionEquivEvaluation

noncomputable section

/-! Evaluation formulas for the elementary equivalences used to encode sheaf maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u v w z

theorem fullyFaithfulHomEquiv_apply {C : Type u} {D : Type v}
    [Category.{w} C] [Category.{z} D] (F : C ⥤ D) (hF : F.FullyFaithful)
    {A B : C} (f : A ⟶ B) : hF.homEquiv f = F.map f := rfl

theorem isoHomCongr_apply {C : Type u} [Category.{v} C]
    {A A' B B' : C} (e : A ≅ A') (d : B ≅ B') (f : A ⟶ B) :
    Iso.homCongr e d f = e.inv ≫ f ≫ d.hom := rfl

theorem unitHomTopSectionsEquiv_apply {X : Scheme.{u}} (M : X.Modules)
    (f : Invertible.Scheme.Modules.unitObj X ⟶ M) :
    UnitHomTopSections.unitHomTopSectionsEquiv M f = f.val.app (op ⊤) (show Γ(X, ⊤) from 1) := rfl

theorem unitHomTopSection_restrict {X : Scheme.{u}} (M : X.Modules)
    (f : Invertible.Scheme.Modules.unitObj X ⟶ M) (U : X.Opens) :
    M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
      (f.val.app (op ⊤) (show Γ(X, ⊤) from 1)) =
      f.val.app (op U) (show Γ(X, U) from 1) := by
  have h := PresheafOfModules.naturality_apply f.val
    (homOfLE (le_top : U ≤ ⊤)).op (show Γ(X, ⊤) from 1)
  change f.val.app (op U) (X.presheaf.map (homOfLE le_top).op 1) = _ at h
  rw [map_one] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.HomSectionEquivEvaluation
