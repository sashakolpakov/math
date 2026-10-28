import OAI.RepresentationTheory.Theta.Adelic.GlobalNormCharacter
import OAI.RepresentationTheory.Theta.Adelic.IdeleCharacterExtension
import OAI.RepresentationTheory.Theta.Adelic.Data

/-! # Characters -/

namespace OAI.RepresentationTheory.Theta.Adelic.Characters

noncomputable section

/-! Full character conclusion for AdelicTheta: closed idele-class embedding,
extension of every base character, and splitting characters with the
prescribed global powers of the constructed quadratic norm character. -/

open scoped _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.IdeleClassInjection OAI.RepresentationTheory.Theta.Adelic.IdeleCharacterExtension
open OAI.RepresentationTheory.Theta.Adelic.GlobalNormCharacter OAI.RepresentationTheory.Theta.Adelic.Data

theorem complete_character_conclusion
    (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0) (hns : ¬ IsSquare d)
    (n m : ℕ) (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ)
    (hu : ∀ x, ‖ψ x‖ = 1) (hn : ∃ x, ψ x ≠ 1)
    (hp : ∀ q : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) q) = 1) :
    ∃ C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d n m, C.ψ = ψ ∧ Data.CharacterConclusion F d n m C := by
  let ε := GlobalNormCharacter.normCharacterClass F d hd ψ hc hu hn hp
  let ω := GlobalNormCharacter.normCharacterAdelic F d hd ψ hc hu hn hp
  obtain ⟨χ, hχp, hχ⟩ := IdeleCharacterExtension.extend_to_quadratic_Hecke_character F d hd hns ε
  have hlocal (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) (a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v)ˣ) :
      Weil.AdelicSplitting.Characters.Construction.localCharacter F d χ v (Weil.AdelicSplitting.Characters.Construction.localScalarIdele F d v a) =
        Weil.AdelicSplitting.Characters.Construction.normCharacter F d v a := by
    change χ (Weil.AdelicSplitting.Characters.Construction.localIdele F d v (Weil.AdelicSplitting.Characters.Construction.localScalarIdele F d v a)) = _
    rw [← BaseLocalIdele.scalar_local_idele, hχ]
    exact GlobalNormCharacter.normCharacterClass_local F d hd ψ hc hu hn hp v a
  let C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d n m := {
    ψ := ψ
    ψ_continuous := hc
    ψ_unitary := hu
    ψ_nontrivial := hn
    ψ_principal := hp
    χV := χ ^ n
    χW := χ ^ m
    χV_principal := by
      intro a
      change (χ ^ n) (IdeleClassInjection.quadraticPrincipal F d a) = 1
      rw [ContinuousMonoidHom.pow_apply, hχp, one_pow]
    χW_principal := by
      intro a
      change (χ ^ m) (IdeleClassInjection.quadraticPrincipal F d a) = 1
      rw [ContinuousMonoidHom.pow_apply, hχp, one_pow]
    χV_restriction := by
      intro v a
      change (χ ^ n) (Weil.AdelicSplitting.Characters.Construction.localIdele F d v (Weil.AdelicSplitting.Characters.Construction.localScalarIdele F d v a)) = _
      rw [ContinuousMonoidHom.pow_apply]
      exact congrArg (fun z : Circle => z ^ n) (hlocal v a)
    χW_restriction := by
      intro v a
      change (χ ^ m) (Weil.AdelicSplitting.Characters.Construction.localIdele F d v (Weil.AdelicSplitting.Characters.Construction.localScalarIdele F d v a)) = _
      rw [ContinuousMonoidHom.pow_apply]
      exact congrArg (fun z : Circle => z ^ m) (hlocal v a) }
  refine ⟨C, rfl, IdeleClassEmbedding.scalarIdeleClass_closedEmbedding F d hd hns,
    fun η => IdeleCharacterExtension.extend_to_quadratic_Hecke_character F d hd hns η, ω,
    GlobalNormCharacter.normCharacterAdelic_principal F d hd ψ hc hu hn hp,
    GlobalNormCharacter.normCharacterAdelic_apply F d hd ψ hc hu hn hp, ?_, ?_⟩
  · intro a
    change (χ ^ n) (IdeleClassInjection.scalarIdele F d a) = ω a ^ n
    rw [ContinuousMonoidHom.pow_apply, hχ]
    rfl
  · intro a
    change (χ ^ m) (IdeleClassInjection.scalarIdele F d a) = ω a ^ m
    rw [ContinuousMonoidHom.pow_apply, hχ]
    rfl

end

end OAI.RepresentationTheory.Theta.Adelic.Characters
