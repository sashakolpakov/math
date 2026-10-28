import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IteratedBaseChangeNaturality

/-! # Inclusion Squares -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.InclusionSquares

/-! Compose the actual inclusion squares through base change and
inverse block isomorphisms. -/

open _root_.CategoryTheory

theorem map_inverse_inclusion {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y A : C} (e : X ≅ Y) (i : Y ⟶ A) (j : X ⟶ A)
    (h : e.hom ≫ i = j) : F.map e.inv ≫ F.map j = F.map i := by
  rw [← F.map_comp, ← h, Iso.inv_hom_id_assoc]

theorem three_iso_inclusion {C : Type*} [Category C]
    {X₀ X₁ X₂ X₃ A₀ A₁ A₂ : C}
    (e₀ : X₀ ≅ X₁) (e₁ : X₁ ≅ X₂) (e₂ : X₂ ≅ X₃)
    (a : A₀ ≅ A₁) (b : A₁ ≅ A₂)
    (i₀ : X₀ ⟶ A₀) (i₁ : X₁ ⟶ A₀) (i₂ : X₂ ⟶ A₁) (i₃ : X₃ ⟶ A₂)
    (h₀ : e₀.hom ≫ i₁ = i₀) (h₁ : e₁.hom ≫ i₂ = i₁ ≫ a.hom)
    (h₂ : e₂.hom ≫ i₃ = i₂ ≫ b.hom) :
    (e₀ ≪≫ e₁ ≪≫ e₂).hom ≫ i₃ = i₀ ≫ (a ≪≫ b).hom := by
  change (e₀.hom ≫ (e₁.hom ≫ e₂.hom)) ≫ i₃ = i₀ ≫ (a.hom ≫ b.hom)
  rw [Category.assoc, Category.assoc, h₂, ← Category.assoc e₁.hom, h₁,
    ← Category.assoc, ← Category.assoc e₀.hom, h₀, Category.assoc]

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.InclusionSquares
