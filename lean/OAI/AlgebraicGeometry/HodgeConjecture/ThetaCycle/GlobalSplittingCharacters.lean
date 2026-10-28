import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.FieldAdelicCharacter
import OAI.RepresentationTheory.Theta.Adelic.GlobalNormCharacter
import OAI.RepresentationTheory.Theta.Adelic.GlobalCharacters

/-! # Global Splitting Characters -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.GlobalSplittingCharacters.CM

noncomputable section

/-! ThetaCycle: construct the full AdelicSplitting global splitting-character package from
the actual trace additive character and the proved quadratic norm character.
No character or local restriction is an additional hypothesis. -/

open scoped _root_.NumberField

variable (F : Type) [Field F] [NumberField F]

theorem exists_field_global_splitting_characters (d : F) (hd : d ≠ 0) (hns : ¬ IsSquare d)
    (n m : ℕ) : ∃ C : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d n m, C.ψ = FieldAdelicCharacter.CM.fieldAdelicCharacter F := by
  let ε := RepresentationTheory.Theta.Adelic.GlobalNormCharacter.normCharacterClass F d hd (FieldAdelicCharacter.CM.fieldAdelicCharacter F)
    (FieldAdelicCharacter.CM.field_adelic_character_continuous F) (FieldAdelicCharacter.CM.field_adelic_character_unitary F)
    (FieldAdelicCharacter.CM.field_adelic_character_nontrivial F) (FieldAdelicCharacter.CM.field_adelic_character_principal F)
  apply RepresentationTheory.Theta.Adelic.GlobalCharacters.globalCharacters_from_base_character F d hd hns n m
    (FieldAdelicCharacter.CM.fieldAdelicCharacter F) (FieldAdelicCharacter.CM.field_adelic_character_continuous F) (FieldAdelicCharacter.CM.field_adelic_character_unitary F)
    (FieldAdelicCharacter.CM.field_adelic_character_nontrivial F) (FieldAdelicCharacter.CM.field_adelic_character_principal F) ε
  intro v a
  exact RepresentationTheory.Theta.Adelic.GlobalNormCharacter.normCharacterClass_local F d hd (FieldAdelicCharacter.CM.fieldAdelicCharacter F)
    (FieldAdelicCharacter.CM.field_adelic_character_continuous F) (FieldAdelicCharacter.CM.field_adelic_character_unitary F)
    (FieldAdelicCharacter.CM.field_adelic_character_nontrivial F) (FieldAdelicCharacter.CM.field_adelic_character_principal F) v a

def fieldGlobalSplittingCharacters (d : F) (hd : d ≠ 0) (hns : ¬ IsSquare d) (n m : ℕ) :
    RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d n m :=
  (exists_field_global_splitting_characters F d hd hns n m).choose

theorem field_global_splitting_characters_additive (d : F) (hd : d ≠ 0) (hns : ¬ IsSquare d) (n m : ℕ) :
    (fieldGlobalSplittingCharacters F d hd hns n m).ψ = FieldAdelicCharacter.CM.fieldAdelicCharacter F :=
  (exists_field_global_splitting_characters F d hd hns n m).choose_spec

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.GlobalSplittingCharacters.CM
