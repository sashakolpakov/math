import OAI.RepresentationTheory.Theta.Adelic.IdeleCharacterExtension
import OAI.RepresentationTheory.Theta.Adelic.BaseLocalIdele

/-! # Global Characters -/

namespace OAI.RepresentationTheory.Theta.Adelic.GlobalCharacters

noncomputable section

/-! AdelicSplitting's actual splitting-character package is constructed from the base
quadratic idele-class character by extension and dimension powers. The
remaining arithmetic input is precisely that base character with its
local norm-kernel restrictions. -/

open scoped _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.IdeleClassInjection
open OAI.RepresentationTheory.Theta.Adelic.IdeleCharacterExtension OAI.RepresentationTheory.Theta.Adelic.BaseLocalIdele

theorem globalCharacters_from_base_character
    (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0) (hns : ¬ IsSquare d)
    (n m : ℕ) (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ)
    (hc : Continuous ψ) (hu : ∀ x, ‖ψ x‖ = 1) (hn : ∃ x, ψ x ≠ 1)
    (hp : ∀ x : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) x) = 1)
    (ε : NumberTheory.Adeles.LocalCompletions.CompletionFactors.IdeleClass F →ₜ* Circle)
    (hε : ∀ v (a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v)ˣ),
      ε (QuotientGroup.mk' (NumberTheory.Adeles.LocalCompletions.CompletionFactors.principalIdele F).range (BaseLocalIdele.baseLocalIdele F v a)) =
        Weil.AdelicSplitting.Characters.Construction.normCharacter F d v a) :
    ∃ C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d n m, C.ψ = ψ := by
  obtain ⟨χ, hχp, hχ⟩ := IdeleCharacterExtension.extend_to_quadratic_Hecke_character F d hd hns ε
  have hlocal (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) (a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v)ˣ) :
      Weil.AdelicSplitting.Characters.Construction.localCharacter F d χ v (Weil.AdelicSplitting.Characters.Construction.localScalarIdele F d v a) = Weil.AdelicSplitting.Characters.Construction.normCharacter F d v a := by
    change χ (Weil.AdelicSplitting.Characters.Construction.localIdele F d v (Weil.AdelicSplitting.Characters.Construction.localScalarIdele F d v a)) = _
    rw [← BaseLocalIdele.scalar_local_idele, hχ, hε]
  refine ⟨{
    ψ := ψ
    ψ_continuous := hc
    ψ_unitary := hu
    ψ_nontrivial := hn
    ψ_principal := hp
    χV := χ ^ n
    χW := χ ^ m
    χV_principal := ?_
    χW_principal := ?_
    χV_restriction := ?_
    χW_restriction := ?_ }, rfl⟩
  · intro a
    change (χ ^ n) (IdeleClassInjection.quadraticPrincipal F d a) = 1
    rw [ContinuousMonoidHom.pow_apply, hχp, one_pow]
  · intro a
    change (χ ^ m) (IdeleClassInjection.quadraticPrincipal F d a) = 1
    rw [ContinuousMonoidHom.pow_apply, hχp, one_pow]
  · intro v a
    change (χ ^ n) (Weil.AdelicSplitting.Characters.Construction.localIdele F d v (Weil.AdelicSplitting.Characters.Construction.localScalarIdele F d v a)) = _
    rw [ContinuousMonoidHom.pow_apply]
    exact congrArg (fun z : Circle => z ^ n) (hlocal v a)
  · intro v a
    change (χ ^ m) (Weil.AdelicSplitting.Characters.Construction.localIdele F d v (Weil.AdelicSplitting.Characters.Construction.localScalarIdele F d v a)) = _
    rw [ContinuousMonoidHom.pow_apply]
    exact congrArg (fun z : Circle => z ^ m) (hlocal v a)

end

end OAI.RepresentationTheory.Theta.Adelic.GlobalCharacters
