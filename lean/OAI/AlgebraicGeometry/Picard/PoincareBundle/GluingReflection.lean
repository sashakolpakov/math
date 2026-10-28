import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.GluingMorphismTransfer

/-! # Gluing Reflection -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.GluingReflection

noncomputable section

/-!
# Faithful affine presentations also reflect gluing compatibility
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

section

variable {C D : Type*} [Category C] [Category D]

/-- A faithful presentation reflects the compatibility encoded by four commuting gluing squares. -/
theorem reflect (F : C ⥤ D) [F.Faithful] {M₁ M₂ N₁ N₂ : C} {X₁ X₂ Y₁ Y₂ : D}
    (c₁ : F.obj M₁ ≅ X₁) (c₂ : F.obj M₂ ≅ X₂)
    (d₁ : F.obj N₁ ≅ Y₁) (d₂ : F.obj N₂ ≅ Y₂)
    (a₁ : M₁ ⟶ N₁) (a₂ : M₂ ⟶ N₂) (σ : M₁ ⟶ M₂) (τ : N₁ ⟶ N₂)
    (p : X₁ ⟶ Y₁) (q : X₂ ⟶ Y₂) (s : X₁ ⟶ X₂) (t : Y₁ ⟶ Y₂)
    (hp : F.map a₁ ≫ d₁.hom = c₁.hom ≫ p)
    (hq : F.map a₂ ≫ d₂.hom = c₂.hom ≫ q)
    (hs : F.map σ ≫ c₂.hom = c₁.hom ≫ s)
    (ht : F.map τ ≫ d₂.hom = d₁.hom ≫ t)
    (h : p ≫ t = s ≫ q) : a₁ ≫ τ = σ ≫ a₂ := by
  apply F.map_injective
  apply (cancel_mono d₂.hom).mp
  calc
    F.map (a₁ ≫ τ) ≫ d₂.hom = F.map a₁ ≫ d₁.hom ≫ t := by
      rw [F.map_comp, Category.assoc, ht]
    _ = c₁.hom ≫ p ≫ t := by rw [← Category.assoc, hp, Category.assoc]
    _ = c₁.hom ≫ s ≫ q := by rw [h]
    _ = F.map σ ≫ c₂.hom ≫ q := by rw [← Category.assoc, ← hs, Category.assoc]
    _ = F.map (σ ≫ a₂) ≫ d₂.hom := by
      rw [F.map_comp, Category.assoc, hq]

end

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Gluing OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.PresentedMorphisms OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.GluingMorphismTransfer

variable {R S : CommRingCat.{u}} (i j : R ⟶ S)

/-- Compatibility of presented geometric maps reflects the exact module gluing equation. -/
theorem affine_reflect {M N : ModuleCat.{u} R} {X Y : (Spec R).Modules}
    (eM : (tilde.functor R).obj M ≅ X) (eN : (tilde.functor R).obj N ≅ Y) (a : M ⟶ N)
    (s : (ModuleCat.extendScalars i.hom).obj M ⟶ (ModuleCat.extendScalars j.hom).obj M)
    (t : (ModuleCat.extendScalars i.hom).obj N ⟶ (ModuleCat.extendScalars j.hom).obj N)
    (σ : (Scheme.Modules.pullback (Spec.map i)).obj X ⟶
      (Scheme.Modules.pullback (Spec.map j)).obj X)
    (τ : (Scheme.Modules.pullback (Spec.map i)).obj Y ⟶
      (Scheme.Modules.pullback (Spec.map j)).obj Y)
    (hs : Affine.GluingMorphismTransfer.IsGluingSquare i j eM s σ) (ht : Affine.GluingMorphismTransfer.IsGluingSquare i j eN t τ)
    (h : Affine.GluingMorphismTransfer.PreservesGeometricGluing i j (Affine.PresentedMorphisms.presentedMap eM eN a) σ τ) :
    (ModuleCat.extendScalars i.hom).map a ≫ t = s ≫ (ModuleCat.extendScalars j.hom).map a :=
  reflect (tilde.functor S)
    (Affine.Gluing.comparison M eM i) (Affine.Gluing.comparison M eM j) (Affine.Gluing.comparison N eN i) (Affine.Gluing.comparison N eN j)
    ((ModuleCat.extendScalars i.hom).map a) ((ModuleCat.extendScalars j.hom).map a) s t
    ((Scheme.Modules.pullback (Spec.map i)).map (Affine.PresentedMorphisms.presentedMap eM eN a))
    ((Scheme.Modules.pullback (Spec.map j)).map (Affine.PresentedMorphisms.presentedMap eM eN a)) σ τ
    (Affine.PresentedMorphisms.comparison_naturality eM eN a i) (Affine.PresentedMorphisms.comparison_naturality eM eN a j) hs ht h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.GluingReflection
