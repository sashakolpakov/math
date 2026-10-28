import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Adjoint Conjugate Normalization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AdjointConjugateNormalization

noncomputable section

/-! Precomposition by a map of left adjoints corresponds to postcomposition by its conjugate on right adjoints. -/
open _root_.CategoryTheory
variable {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}

theorem adjunction_homEquiv_precomp_conjugate (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : L₂ ⟶ L₁) {X : C} {Y : D} (φ : L₁.obj X ⟶ Y) :
    adj₂.homEquiv X Y (α.app X ≫ φ) =
      adj₁.homEquiv X Y φ ≫ (conjugateEquiv adj₁ adj₂ α).app Y := by
  let t := conjugateEquiv adj₁ adj₂ α
  have hu : adj₁.unit.app X ≫ t.app (L₁.obj X) = adj₂.unit.app X ≫ R₂.map (α.app X) :=
    unit_conjugateEquiv adj₁ adj₂ α X
  calc
    adj₂.homEquiv X Y (α.app X ≫ φ) =
        (adj₂.unit.app X ≫ R₂.map (α.app X)) ≫ R₂.map φ := by
      rw [Adjunction.homEquiv_unit, R₂.map_comp, ← Category.assoc]
    _ = (adj₁.unit.app X ≫ t.app (L₁.obj X)) ≫ R₂.map φ :=
      congrArg (fun z => z ≫ R₂.map φ) hu.symm
    _ = (adj₁.unit.app X ≫ R₁.map φ) ≫ t.app Y := by
      rw [Category.assoc, ← t.naturality φ, ← Category.assoc]
    _ = _ := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AdjointConjugateNormalization
