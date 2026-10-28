import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-! # Adjoint Composition -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointComposition

noncomputable section

/-!
# Pasting canonical comparisons of left adjoints
-/

open _root_.CategoryTheory

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]

/-- Appending an adjunction to a canonical composition comparison gives the whiskered comparison. -/
theorem postcompose
    {L₀₁ : A ⥤ B} {R₁₀ : B ⥤ A} {L₁₂ : B ⥤ C} {R₂₁ : C ⥤ B}
    {L₀₂ : A ⥤ C} {R₂₀ : C ⥤ A} {L₂₃ : C ⥤ D} {R₃₂ : D ⥤ C}
    (a : L₀₁ ⊣ R₁₀) (b : L₁₂ ⊣ R₂₁) (c : L₀₂ ⊣ R₂₀) (d : L₂₃ ⊣ R₃₂)
    (e : R₂₁ ⋙ R₁₀ ≅ R₂₀) :
    Adjunction.leftAdjointCompIso a (b.comp d) (c.comp d)
        (Functor.associator R₃₂ R₂₁ R₁₀ ≪≫ Functor.isoWhiskerLeft R₃₂ e) =
      (Functor.associator L₀₁ L₁₂ L₂₃).symm ≪≫
        Functor.isoWhiskerRight (Adjunction.leftAdjointCompIso a b c e) L₂₃ := by
  apply Iso.ext_inv
  apply (conjugateEquiv (a.comp (b.comp d)) (c.comp d)).injective
  change _ = conjugateEquiv (a.comp (b.comp d)) (c.comp d)
    (Functor.whiskerRight (Adjunction.leftAdjointCompIso a b c e).inv L₂₃ ≫
      (Functor.associator L₀₁ L₁₂ L₂₃).hom)
  rw [← conjugateEquiv_comp _ ((a.comp b).comp d), conjugateEquiv_associator_hom,
    conjugateEquiv_whiskerRight, Adjunction.conjugateEquiv_leftAdjointCompIso_inv]
  rw [Adjunction.conjugateEquiv_leftAdjointCompIso_inv]
  rfl

/-- The inverse associator has the inverse right-adjoint associator as its mate. -/
theorem associator_inv
    {L₀₁ : A ⥤ B} {R₁₀ : B ⥤ A} {L₁₂ : B ⥤ C} {R₂₁ : C ⥤ B}
    {L₂₃ : C ⥤ D} {R₃₂ : D ⥤ C}
    (a : L₀₁ ⊣ R₁₀) (b : L₁₂ ⊣ R₂₁) (c : L₂₃ ⊣ R₃₂) :
    conjugateEquiv ((a.comp b).comp c) (a.comp (b.comp c))
      (Functor.associator L₀₁ L₁₂ L₂₃).inv = (Functor.associator R₃₂ R₂₁ R₁₀).inv := by
  have h : conjugateIsoEquiv (a.comp (b.comp c)) ((a.comp b).comp c)
      (Functor.associator L₀₁ L₁₂ L₂₃) = Functor.associator R₃₂ R₂₁ R₁₀ :=
    Iso.ext (conjugateEquiv_associator_hom a b c)
  exact congrArg Iso.inv h

/-- Pasting two right-adjoint comparisons gives the corresponding composite of left comparisons. -/
theorem paste
    {L₀₁ : A ⥤ B} {R₁₀ : B ⥤ A} {L₁₂ : B ⥤ C} {R₂₁ : C ⥤ B}
    {L₂₃ : C ⥤ D} {R₃₂ : D ⥤ C} {L₁₃ : B ⥤ D} {R₃₁ : D ⥤ B}
    {L₀₃ : A ⥤ D} {R₃₀ : D ⥤ A}
    (a : L₀₁ ⊣ R₁₀) (b : L₁₂ ⊣ R₂₁) (c : L₂₃ ⊣ R₃₂)
    (d : L₁₃ ⊣ R₃₁) (v : L₀₃ ⊣ R₃₀)
    (e : R₃₂ ⋙ R₂₁ ≅ R₃₁) (k : R₃₁ ⋙ R₁₀ ≅ R₃₀) :
    Adjunction.leftAdjointCompIso (a.comp b) c v
        ((Functor.associator R₃₂ R₂₁ R₁₀).symm ≪≫
          Functor.isoWhiskerRight e R₁₀ ≪≫ k) =
      Functor.associator L₀₁ L₁₂ L₂₃ ≪≫
        Functor.isoWhiskerLeft L₀₁ (Adjunction.leftAdjointCompIso b c d e) ≪≫
          Adjunction.leftAdjointCompIso a d v k := by
  apply Iso.ext_inv
  apply (conjugateEquiv ((a.comp b).comp c) v).injective
  simp only [Iso.trans_inv, Functor.isoWhiskerLeft_inv, Category.assoc]
  rw [← conjugateEquiv_comp _ (a.comp d),
    ← conjugateEquiv_comp _ (a.comp (b.comp c)), associator_inv,
    conjugateEquiv_whiskerLeft]
  simp only [Adjunction.conjugateEquiv_leftAdjointCompIso_inv]
  exact (Category.assoc _ _ _).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointComposition
