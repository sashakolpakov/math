import OAI.RepresentationTheory.Theta.Adelic.FiniteCharacterNontrivial
import OAI.RepresentationTheory.Weil.AdelicSplitting.BaseChange

/-! # Unramified Annihilator -/

namespace OAI.RepresentationTheory.Theta.Adelic.UnramifiedAnnihilator

noncomputable section

/-! The standard local integer lattice is its character annihilator at
almost every finite place, independently of normalized local splittings. -/

open Filter
open scoped _root_.NumberField Classical
open _root_.NumberField IsDedekindDomain

open OAI.RepresentationTheory.Weil.AdelicSplitting.BaseChange.Construction
open OAI.RepresentationTheory.Theta.Adelic.FiniteCharacterAnnihilator OAI.RepresentationTheory.Theta.Adelic.FiniteCharacterNontrivial

theorem local_annihilator_integer
    (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ)
    (hu : ∀ a, ‖ψ a‖ = 1) (hn : ∃ a, ψ a ≠ 1)
    (hp : ∀ q : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) q) = 1) :
    ∀ᶠ v in cofinite, ∀ u : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v,
      (∀ t ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v, Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ v (u * t) = 1) →
        u ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F v := by
  obtain ⟨r, hr, hbound⟩ := FiniteCharacterNontrivial.integralAnnihilator_denominator F ψ hc hu hn hp
  let q := algebraMap (𝓞 F) F r
  have hq : q ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hr
  filter_upwards [Weil.AdelicSplitting.Integral.Construction.rationalScalar_integral F q⁻¹] with v hv
  intro u hlocal
  cases v with
  | inl v => exact Subring.mem_top _
  | inr v =>
    let a : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F := RestrictedProduct.single
      (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v u
    have ha : a ∈ FiniteCharacterAnnihilator.integralAnnihilator F ψ := by
      intro b
      have he : a * b.val = RestrictedProduct.single
          (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v (u * b.val v) :=
        (RestrictedProduct.single_mul _ v u b.val).symm
      rw [he]
      exact hlocal (b.val v) (b.property v)
    have h := hbound a ha v
    change algebraMap (𝓞 F) (v.adicCompletion F) r * a v ∈ v.adicCompletionIntegers F at h
    have hav : a v = u := RestrictedProduct.single_eq_same _ _ _
    rw [hav, IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)] at h
    have hrmul : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) q * u ∈ Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v) := h
    have hi := (Weil.AdelicSplitting.Integral.Construction.localIntegerRing F (.inr v)).mul_mem hv hrmul
    have he : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) q⁻¹ * (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inr v) q * u) = u := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hq, map_one, one_mul]
    rwa [he] at hi

end

end OAI.RepresentationTheory.Theta.Adelic.UnramifiedAnnihilator
