import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-! # Unramified Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedSections

noncomputable section

/-! A section of an unramified morphism is an open immersion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem section_isOpenImmersion_of_unramified {X S : Scheme.{u}} (p : X ⟶ S)
    [LocallyOfFiniteType p] [FormallyUnramified p] (x : S ⟶ X) (hx : x ≫ p = 𝟙 S) :
    IsOpenImmersion x := by
  have : MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFiniteType.{u} ⊓ @FormallyUnramified.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.inf
      (P := @LocallyOfFiniteType.{u}) (Q := @FormallyUnramified.{u})
  have : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion.{u}
      (@LocallyOfFiniteType.{u} ⊓ @FormallyUnramified.{u}) := by
    rw [MorphismProperty.hasOfPostcompProperty_iff_le_diagonal]
    intro Y Z f ⟨_, _⟩
    exact inferInstanceAs (IsOpenImmersion (Limits.pullback.diagonal f))
  have : IsOpenImmersion (x ≫ p) := by rw [hx]; infer_instance
  exact MorphismProperty.of_postcomp (W := @IsOpenImmersion)
    (W' := @LocallyOfFiniteType ⊓ @FormallyUnramified) x p ⟨inferInstance, inferInstance⟩ inferInstance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.UnramifiedSections
