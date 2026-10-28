import OAI.RepresentationTheory.Theta.Adelic.LocalNormCharacter
import OAI.RepresentationTheory.Theta.Adelic.NormCharacterReciprocity
import OAI.RepresentationTheory.Theta.Adelic.NormCharacterUnramified
import OAI.RepresentationTheory.Theta.Adelic.IdeleCharacterProduct

/-! # Global Norm Character -/

namespace OAI.RepresentationTheory.Theta.Adelic.GlobalNormCharacter

noncomputable section

/-! The global quadratic norm character is the finite product of the
actual local norm criteria; its principal triviality is proved by Gaussian
reciprocity and it descends continuously to the base idele class group. -/

open scoped _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.IdeleCharacterProduct

variable (F : Type) [Field F] [NumberField F] (d : F) (hd : d ≠ 0)

def localCharacter (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v)ˣ →ₜ* Circle :=
  LocalNormCharacter.localNormCharacter (Weil.AdelicSplitting.LocalKernel.Construction.completion_nondiscrete F v)
    (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v d) ((map_ne_zero (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v)).mpr hd)

theorem localCharacter_apply (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) (a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v)ˣ) :
    localCharacter F d hd v a = Weil.AdelicSplitting.Characters.Construction.normCharacter F d v a := rfl

variable (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ x, ‖ψ x‖ = 1)
variable (hn : ∃ x, ψ x ≠ 1) (hp : ∀ q : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) q) = 1)

def normCharacterAdelic : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)ˣ →ₜ* Circle :=
  IdeleCharacterProduct.productCharacter F (localCharacter F d hd)
    (NormCharacterUnramified.normCharacter_unramified F ψ hc hu hn hp d hd)

theorem normCharacterAdelic_apply (a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F)ˣ) :
    normCharacterAdelic F d hd ψ hc hu hn hp a =
      ∏ᶠ v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F, Weil.AdelicSplitting.Characters.Construction.normCharacter F d v (Units.map (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.evaluate F v).toMonoidHom a) := rfl

theorem normCharacterAdelic_local (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) (a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v)ˣ) :
    normCharacterAdelic F d hd ψ hc hu hn hp (BaseLocalIdele.baseLocalIdele F v a) =
      Weil.AdelicSplitting.Characters.Construction.normCharacter F d v a :=
  IdeleCharacterProduct.productCharacter_local F (localCharacter F d hd) _ v a

theorem normCharacterAdelic_principal (a : Fˣ) :
    normCharacterAdelic F d hd ψ hc hu hn hp (NumberTheory.Adeles.LocalCompletions.CompletionFactors.principalIdele F a) = 1 := by
  let χ := localCharacter F d hd
  let b := NumberTheory.Adeles.LocalCompletions.CompletionFactors.principalIdele F a
  have hf := IdeleCharacterProduct.localFactors_finite F χ
    (NormCharacterUnramified.normCharacter_unramified F ψ hc hu hn hp d hd) b
  have hfc : Function.HasFiniteMulSupport (fun v => (χ v (IdeleCharacterProduct.unitEvaluate F v b) : ℂ)) :=
    hf.subset (fun v hv he => hv (congrArg (fun z : Circle => (z : ℂ)) he))
  have he (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) : (χ v (IdeleCharacterProduct.unitEvaluate F v b) : ℂ) =
      (Weil.AdelicSplitting.Characters.Construction.normCharacter F d v (Units.map (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F v).toMonoidHom a) : ℂ) := rfl
  apply Circle.coe_injective
  change Circle.coeHom (∏ᶠ v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F, χ v (IdeleCharacterProduct.unitEvaluate F v b)) = 1
  rw [Circle.coeHom.map_finprod hf]
  change (∏ᶠ v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F, (χ v (IdeleCharacterProduct.unitEvaluate F v b) : ℂ)) = 1
  rw [← tprod_eq_finprod (L := SummationFilter.unconditional (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F)) hfc]
  have h := NormCharacterReciprocity.normCharacter_principal_hasProd F ψ hc hu hn hp d hd a
  exact (h.congr_fun he).tprod_eq

def normCharacterClass : NumberTheory.Adeles.LocalCompletions.CompletionFactors.IdeleClass F →ₜ* Circle :=
  { QuotientGroup.lift (NumberTheory.Adeles.LocalCompletions.CompletionFactors.principalIdele F).range
      (normCharacterAdelic F d hd ψ hc hu hn hp).toMonoidHom
      (by rintro x ⟨a, rfl⟩; exact normCharacterAdelic_principal F d hd ψ hc hu hn hp a) with
    continuous_toFun := by
      apply isQuotientMap_quotient_mk'.continuous_iff.mpr
      exact (normCharacterAdelic F d hd ψ hc hu hn hp).continuous }

theorem normCharacterClass_local (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) (a : (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v)ˣ) :
    normCharacterClass F d hd ψ hc hu hn hp
      (QuotientGroup.mk' (NumberTheory.Adeles.LocalCompletions.CompletionFactors.principalIdele F).range
        (BaseLocalIdele.baseLocalIdele F v a)) = Weil.AdelicSplitting.Characters.Construction.normCharacter F d v a :=
  normCharacterAdelic_local F d hd ψ hc hu hn hp v a

end

end OAI.RepresentationTheory.Theta.Adelic.GlobalNormCharacter
