import OAI.RepresentationTheory.Theta.Adelic.FiniteCharacterAnnihilator
import OAI.RepresentationTheory.Theta.Adelic.CharacterDualLattice
import OAI.RepresentationTheory.Theta.Adelic.ArchimedeanNontrivial

/-! # Finite Character Nontrivial -/

namespace OAI.RepresentationTheory.Theta.Adelic.FiniteCharacterNontrivial

noncomputable section

/-! Nontriviality at every finite place follows from principal triviality,
finite strong approximation, and the rational dual integer lattice. -/

open scoped _root_.NumberField Classical _root_.Topology
open _root_.NumberField IsDedekindDomain

open OAI.RepresentationTheory.Theta.Adelic.FiniteCharacterAnnihilator OAI.RepresentationTheory.Theta.Adelic.CharacterDualLattice
open OAI.RepresentationTheory.Theta.Adelic.GlobalCharacterNontrivial OAI.RepresentationTheory.Theta.Adelic.RationalCharacterPairing

variable (F : Type) [Field F] [NumberField F]

theorem integralAnnihilator_denominator
    (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ)
    (hu : ∀ a, ‖ψ a‖ = 1) (hn : ∃ a, ψ a ≠ 1)
    (hp : ∀ q : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) q) = 1) :
    ∃ r : 𝓞 F, r ≠ 0 ∧ ∀ a ∈ FiniteCharacterAnnihilator.integralAnnihilator F ψ,
      algebraMap (𝓞 F) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) r * a ∈ Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F := by
  obtain ⟨L, hL0, hL, hrat⟩ := GlobalCharacterNontrivial.exists_nonzero_archimedean_linear_character F ψ hc hp hu hn
  obtain ⟨ℓ, hℓ⟩ := RationalCharacterPairing.rational_functional F L hrat
  have hℓ0 : ℓ ≠ 0 := by
    intro hz
    apply hL0
    apply (mixedEmbedding.latticeBasis F).ext
    intro i
    change L (mixedEmbedding.latticeBasis F i) = 0
    rw [mixedEmbedding.latticeBasis_apply, ← hℓ, hz, LinearMap.zero_apply, Rat.cast_zero]
  obtain ⟨r, hr, hbound⟩ := CharacterDualLattice.rational_dual_lattice_denominator F ℓ hℓ0
  refine ⟨r, hr, fun a => ?_⟩
  have hclosed : IsClosed {a : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F | a ∈ FiniteCharacterAnnihilator.integralAnnihilator F ψ →
      algebraMap (𝓞 F) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) r * a ∈ Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F} := by
    have hmul : Continuous (fun a : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F => algebraMap (𝓞 F) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) r * a) :=
      continuous_const.mul continuous_id
    have h := (FiniteCharacterAnnihilator.integralAnnihilator_isOpen F ψ hc hu).isClosed_compl.union
      (((Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F).toAddSubgroup.isClosed_of_isOpen
        (Weil.AdelicSplitting.IntegralAdeles.Construction.isOpen_finiteIntegralRing F)).preimage hmul)
    convert h using 1
    ext a
    change (a ∈ FiniteCharacterAnnihilator.integralAnnihilator F ψ →
      algebraMap (𝓞 F) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) r * a ∈ Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F) ↔
      (a ∉ FiniteCharacterAnnihilator.integralAnnihilator F ψ ∨
        algebraMap (𝓞 F) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) r * a ∈ Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F)
    exact imp_iff_not_or
  apply (Weil.AdelicSplitting.StrongApproximation.Construction.denseRange_rational_finiteAdeles F).induction_on
    (p := fun a : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F => a ∈ FiniteCharacterAnnihilator.integralAnnihilator F ψ →
      algebraMap (𝓞 F) (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) r * a ∈ Weil.AdelicSplitting.IntegralAdeles.Construction.finiteIntegralRing F) a hclosed
  intro q hq
  have hi := (FiniteCharacterAnnihilator.rational_mem_integralAnnihilator_iff F ψ hc hp L hL q).mp hq
  obtain ⟨s, hs⟩ := hbound q (fun b => by
    obtain ⟨z, hz⟩ := hi b
    refine ⟨z, ?_⟩
    exact_mod_cast hz.trans (hℓ _).symm)
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F), ← map_mul, ← hs,
    ← IsScalarTower.algebraMap_apply]
  exact Weil.AdelicSplitting.IntegralAdeles.Construction.algebraMap_mem_finiteIntegralRing F s

theorem finite_character_nontrivial
    (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ)
    (hu : ∀ a, ‖ψ a‖ = 1) (hn : ∃ a, ψ a ≠ 1)
    (hp : ∀ q : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) q) = 1)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ t : v.adicCompletion F, Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ (.inr v) t ≠ 1 := by
  by_contra hlocal
  simp only [not_exists, not_not] at hlocal
  obtain ⟨r, hr, hbound⟩ := integralAnnihilator_denominator F ψ hc hu hn hp
  have hsingle (t : v.adicCompletion F) :
      RestrictedProduct.single (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v t ∈
        FiniteCharacterAnnihilator.integralAnnihilator F ψ := by
    intro b
    let a : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F := RestrictedProduct.single
      (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v t
    change FiniteCharacterAnnihilator.finiteCharacter F ψ (a * b.val) = 1
    have he : a * b.val = RestrictedProduct.single
        (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v (t * b.val v) :=
      (RestrictedProduct.single_mul _ v t b.val).symm
    rw [he]
    exact hlocal (t * b.val v)
  have hrF : algebraMap (𝓞 F) F r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hr
  have hrv : algebraMap (𝓞 F) (v.adicCompletion F) r ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
    exact (map_ne_zero_iff _ (algebraMap F (v.adicCompletion F)).injective).mpr hrF
  obtain ⟨q, hq⟩ := v.valuation_surjective F (WithZero.exp 1)
  let t := algebraMap F (v.adicCompletion F) q
  have ht : t ∉ v.adicCompletionIntegers F := by
    change ¬ Valued.v (q : v.adicCompletion F) ≤ 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hq]
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  have h := hbound _ (hsingle (t / algebraMap (𝓞 F) (v.adicCompletion F) r)) v
  change algebraMap (𝓞 F) (v.adicCompletion F) r *
    (RestrictedProduct.single
      (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v
      (t / algebraMap (𝓞 F) (v.adicCompletion F) r)) v ∈ v.adicCompletionIntegers F at h
  rw [RestrictedProduct.single_eq_same] at h
  have he : algebraMap (𝓞 F) (v.adicCompletion F) r *
      (t / algebraMap (𝓞 F) (v.adicCompletion F) r) = t := by
    field_simp
  rw [he] at h
  exact ht h

theorem local_character_nontrivial
    (ψ : AddChar (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ)
    (hu : ∀ a, ‖ψ a‖ = 1) (hn : ∃ a, ψ a ≠ 1)
    (hp : ∀ q : F, ψ (algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Adeles F) q) = 1) (v : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places F) :
    ∃ t : Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F v, Weil.AdelicSplitting.Characters.Construction.localAdditiveCharacter F ψ v t ≠ 1 := by
  cases v with
  | inl v => exact ArchimedeanNontrivial.archimedean_character_nontrivial F ψ hc hu hn hp v
  | inr v => exact finite_character_nontrivial F ψ hc hu hn hp v

end

end OAI.RepresentationTheory.Theta.Adelic.FiniteCharacterNontrivial
