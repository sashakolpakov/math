import Mathlib.CategoryTheory.NatIso

/-! # Gluing Squares -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.GluingSquares

noncomputable section

/-!
# Transport a gluing-compatible morphism through four comparison squares
-/

open _root_.CategoryTheory

variable {C D : Type*} [Category C] [Category D]

/-- A conjugated gluing equation gives its commuting comparison square. -/
theorem unconjugate {X Y U V : D} (c : X ≅ U) (d : Y ≅ V) (a : X ⟶ Y) (b : U ⟶ V)
    (h : a = c.hom ≫ b ≫ d.inv) : a ≫ d.hom = c.hom ≫ b := by
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Four comparison squares retain the full gluing compatibility of a morphism. -/
theorem transfer (F : C ⥤ D) {M₁ M₂ N₁ N₂ : C} {X₁ X₂ Y₁ Y₂ : D}
    (c₁ : F.obj M₁ ≅ X₁) (c₂ : F.obj M₂ ≅ X₂)
    (d₁ : F.obj N₁ ≅ Y₁) (d₂ : F.obj N₂ ≅ Y₂)
    (a₁ : M₁ ⟶ N₁) (a₂ : M₂ ⟶ N₂) (σ : M₁ ⟶ M₂) (τ : N₁ ⟶ N₂)
    (p : X₁ ⟶ Y₁) (q : X₂ ⟶ Y₂) (s : X₁ ⟶ X₂) (t : Y₁ ⟶ Y₂)
    (hp : F.map a₁ ≫ d₁.hom = c₁.hom ≫ p)
    (hq : F.map a₂ ≫ d₂.hom = c₂.hom ≫ q)
    (hs : F.map σ ≫ c₂.hom = c₁.hom ≫ s)
    (ht : F.map τ ≫ d₂.hom = d₁.hom ≫ t)
    (h : a₁ ≫ τ = σ ≫ a₂) : p ≫ t = s ≫ q := by
  apply (cancel_epi c₁.hom).mp
  calc
    c₁.hom ≫ p ≫ t = (F.map a₁ ≫ d₁.hom) ≫ t := by rw [hp, Category.assoc]
    _ = F.map a₁ ≫ F.map τ ≫ d₂.hom := by rw [Category.assoc, ht]
    _ = F.map (a₁ ≫ τ) ≫ d₂.hom := by rw [F.map_comp, Category.assoc]
    _ = F.map (σ ≫ a₂) ≫ d₂.hom := congrArg (fun z => F.map z ≫ d₂.hom) h
    _ = F.map σ ≫ c₂.hom ≫ q := by rw [F.map_comp, Category.assoc, hq]
    _ = c₁.hom ≫ s ≫ q := by rw [← Category.assoc, hs, Category.assoc]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.GluingSquares
