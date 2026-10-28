import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-! # Adjunction Coherence -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.AdjunctionCoherence.Construction

/-! # Completion: compatibility of adjoint maps with comparison isomorphisms -/

open _root_.CategoryTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}

/-- Transporting a map through a left-adjoint comparison transports its
adjoint through the corresponding right-adjoint comparison. -/
theorem adjunction_mate_homEquiv (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (τ : L₂ ⟶ L₁) {X : C} {Y : D} (f : L₁.obj X ⟶ Y) :
    a₂.homEquiv X Y (τ.app X ≫ f) =
      a₁.homEquiv X Y f ≫ (conjugateEquiv a₁ a₂ τ).app Y := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv, Category.assoc,
    ← (conjugateEquiv a₁ a₂ τ).naturality, ← Category.assoc,
    ← Adjunction.homEquiv_unit]

variable {B : Type*} [Category* B]
    {L₀₁ : B ⥤ C} {R₁₀ : C ⥤ B}
    {L₁₂ : C ⥤ D} {R₂₁ : D ⥤ C}
    {L₀₂ : B ⥤ D} {R₂₀ : D ⥤ B}

/-- Composite adjoint maps are compatible with the adjoint comparison iso. -/
theorem adjunction_comp_adjoint (a₀₁ : L₀₁ ⊣ R₁₀) (a₁₂ : L₁₂ ⊣ R₂₁)
    (a₀₂ : L₀₂ ⊣ R₂₀) (e : R₂₁ ⋙ R₁₀ ≅ R₂₀)
    {X : B} {Y : C} {Z : D}
    (f : X ⟶ R₁₀.obj Y) (g : Y ⟶ R₂₁.obj Z) :
    (Adjunction.leftAdjointCompIso a₀₁ a₁₂ a₀₂ e).hom.app X ≫
        (a₀₂.homEquiv X Z).symm (f ≫ R₁₀.map g ≫ e.hom.app Z) =
      L₁₂.map ((a₀₁.homEquiv X Y).symm f) ≫ (a₁₂.homEquiv Y Z).symm g := by
  apply ((a₀₁.comp a₁₂).homEquiv X Z).injective
  rw [adjunction_mate_homEquiv a₀₂ (a₀₁.comp a₁₂)]
  simp only [Equiv.apply_symm_apply]
  change (f ≫ R₁₀.map g ≫ e.hom.app Z) ≫
    ((conjugateEquiv a₀₂ (a₀₁.comp a₁₂))
      ((conjugateEquiv a₀₂ (a₀₁.comp a₁₂)).symm e.inv)).app Z = _
  rw [Equiv.apply_symm_apply]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  rw [Adjunction.comp_homEquiv]
  change _ = a₀₁.homEquiv X (R₂₁.obj Z)
    (a₁₂.homEquiv (L₀₁.obj X) Z
      (L₁₂.map ((a₀₁.homEquiv X Y).symm f) ≫ (a₁₂.homEquiv Y Z).symm g))
  rw [a₁₂.homEquiv_naturality_left, Equiv.apply_symm_apply,
    a₀₁.homEquiv_naturality_right, Equiv.apply_symm_apply]

theorem adjunction_id_adjoint {L R : C ⥤ C} (a : L ⊣ R) (e : R ≅ 𝟭 C) (X : C) :
    (a.homEquiv X X).symm (e.inv.app X) = (a.leftAdjointIdIso e).hom.app X := by
  apply (a.homEquiv X X).injective
  rw [Equiv.apply_symm_apply]
  have h := adjunction_mate_homEquiv (Adjunction.id (C := C)) a
    (a.leftAdjointIdIso e).hom (𝟙 X)
  have hid : (Adjunction.id (C := C)).homEquiv X X (𝟙 X) = 𝟙 X := by
    rw [Adjunction.homEquiv_unit]
    exact Category.id_comp _
  rw [hid] at h
  simpa using h.symm

end OAI.AlgebraicGeometry.FormalGeometry.Completion.AdjunctionCoherence.Construction
