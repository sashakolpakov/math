import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterFamily

/-! # Character Family Square -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CharacterFamilySquare.Family

noncomputable section

/-! CartierDuality's actual character-line family coordinates commute with the original product cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterFamily.Construction.KernelCharacters

variable {S : Scheme.{u}} {A B : Over S} (f : A ⟶ B) (Q : Over S)

/-- The character-family map is the actual fiber-product interchange isomorphism. -/
theorem familyMap_isIso : IsIso (AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B Q) := by
  rw [AbelianScheme.CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterFamilyMap_eq_symmetry]
  infer_instance

/-- The original parameter product cover is exactly the base-changed cover in CartierDuality coordinates. -/
theorem square :
    AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap A Q ≫ ((Over.pullback Q.hom).map f).left =
      (𝟙 Q ⊗ₘ f).left ≫ AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B Q := by
  apply pullback.hom_ext
  · simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst, AbelianScheme.CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterFamilyMap_fst]
    rw [← Category.assoc, AbelianScheme.CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterFamilyMap_fst]
    exact (congrArg Over.Hom.left (tensorHom_snd (𝟙 Q) f)).symm
  · simp only [Category.assoc, Over.pullback_map_left, pullback.lift_snd, AbelianScheme.CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterFamilyMap_snd]
    exact (congrArg Over.Hom.left
      ((tensorHom_fst (𝟙 Q) f).trans (Category.comp_id (fst Q A)))).symm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CharacterFamilySquare.Family
