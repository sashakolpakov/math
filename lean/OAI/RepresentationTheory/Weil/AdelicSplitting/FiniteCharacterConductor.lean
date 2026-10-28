import OAI.RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles
import OAI.RepresentationTheory.Weil.AdelicSplitting.UnramifiedCharacter
import OAI.RepresentationTheory.Weil.AdelicSplitting.CharacterProduct
import OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanIntertwiner

/-! # Finite Character Conductor -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteCharacterConductor.Construction

noncomputable section

/-! An integral conductor for the finite part of the supplied global
character. It is derived from compact local integer rings and the proved
almost-everywhere unramified character property. -/

open scoped _root_.NumberField Classical _root_.Topology
open IsDedekindDomain Filter

private theorem compact_character_exponent
    {A : Type*} [AddCommGroup A] [TopologicalSpace A] [CompactSpace A]
    (χ : AddChar A Circle) (hχ : IsLocallyConstant χ) :
    ∃ n : ℕ, 0 < n ∧ ∀ x : A, χ x ^ n = 1 := by
  let S := χ.toMonoidHom.range
  have hS : Set.Finite (S : Set Circle) := by
    have h := (LocallyConstant.mk χ hχ).range_finite
    change (Set.range χ).Finite at h
    have he : (S : Set Circle) = Set.range χ := by
      ext z
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨x.toAdd, hx⟩
      · rintro ⟨x, hx⟩
        exact ⟨Multiplicative.ofAdd x, hx⟩
    rwa [he]
  let : Fintype S := hS.fintype
  refine ⟨Fintype.card S, Fintype.card_pos, fun x => ?_⟩
  have h := pow_card_eq_one (x := χ.toMonoidHom.rangeRestrict (Multiplicative.ofAdd x))
  exact congrArg (fun z : S => (z : Circle)) h

variable (F : Type) [Field F] [NumberField F]

theorem local_integer_character_exponent
    (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ a, ‖ψ a‖ = 1)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ n : ℕ, 0 < n ∧ ∀ x ∈ v.adicCompletionIntegers F,
      Characters.Construction.localAdditiveCharacter F ψ (.inr v) x ^ n = 1 := by
  let ψv := Characters.Construction.localAdditiveCharacter F ψ (.inr v)
  let χ : AddChar (v.adicCompletionIntegers F) Circle :=
    { toFun := fun x => ⟨ψv x.val, mem_sphere_zero_iff_norm.mpr
        (Characters.Construction.localAdditiveCharacter_unitary F ψ hu (.inr v) x.val)⟩
      map_zero_eq_one' := Subtype.ext ψv.map_zero_eq_one
      map_add_eq_mul' := fun x y => Subtype.ext (ψv.map_add_eq_mul x.val y.val) }
  have hψv : IsLocallyConstant (fun x : v.adicCompletion F => ψv x) :=
    NonarchimedeanIntertwiner.LocalAnalysis.nonarchimedean_character_locallyConstant ψv
      (Characters.Construction.localAdditiveCharacter_unitary F ψ hu (.inr v))
      (Characters.Construction.localAdditiveCharacter_continuous F ψ hc (.inr v))
  have hχ : IsLocallyConstant χ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hh := (hψv.comp_continuous continuous_subtype_val).eventually_eq x
    filter_upwards [hh] with y hy
    exact Subtype.ext hy
  obtain ⟨n, hn, h⟩ := compact_character_exponent χ hχ
  refine ⟨n, hn, fun x hx => ?_⟩
  exact congrArg (fun z : Circle => (z : ℂ)) (h ⟨x, hx⟩)

theorem exists_finite_character_conductor
    (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ) (hc : Continuous ψ) (hu : ∀ a, ‖ψ a‖ = 1) :
    ∃ M : ℕ, 0 < M ∧ ∀ a : IntegralAdeles.Construction.finiteIntegralRing F,
      ψ ((0, (M : ArchimedeanAdeles.Construction.FiniteAdeles F) * a.val) : ArchimedeanAdeles.Construction.Adeles F) = 1 := by
  have htail := UnramifiedCharacter.Construction.localAdditiveCharacter_unramified_finite F ψ hu hc
  have hs := eventually_cofinite.mp htail
  let s := hs.toFinset
  choose k hk hkv using local_integer_character_exponent F ψ hc hu
  let M : ℕ := ∏ v ∈ s, k v
  have hM : 0 < M := Finset.prod_pos (fun v _ => hk v)
  refine ⟨M, hM, fun a => ?_⟩
  let b : ArchimedeanAdeles.Construction.Adeles F := (0, (M : ArchimedeanAdeles.Construction.FiniteAdeles F) * a.val)
  have hlocal : ∀ w : ArchimedeanAdeles.Construction.Places F, Characters.Construction.localAdditiveCharacter F ψ w (ArchimedeanAdeles.Construction.evaluate F w b) = 1 := by
    intro w
    cases w with
    | inl v => exact (Characters.Construction.localAdditiveCharacter F ψ (.inl v)).map_zero_eq_one
    | inr v =>
      change Characters.Construction.localAdditiveCharacter F ψ (.inr v) ((M : v.adicCompletion F) * a.val v) = 1
      by_cases hv : v ∈ s
      · obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem k hv
        change M = k v * t at ht
        rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow, ht, pow_mul, hkv v _ (a.property v), one_pow]
      · have hv' : ∀ x ∈ v.adicCompletionIntegers F,
            Characters.Construction.localAdditiveCharacter F ψ (.inr v) x = 1 := by simpa [s] using hv
        exact hv' _ ((v.adicCompletionIntegers F).toSubring.mul_mem
          (natCast_mem _ M) (a.property v))
  have hp := CharacterProduct.Construction.localAdditiveCharacter_hasProd F ψ hc b
  have hconst : HasProd (fun w : ArchimedeanAdeles.Construction.Places F => Characters.Construction.localAdditiveCharacter F ψ w (ArchimedeanAdeles.Construction.evaluate F w b)) 1 := by
    simpa only [hlocal] using (hasProd_one : HasProd (fun _ : ArchimedeanAdeles.Construction.Places F => (1 : ℂ)) 1)
  exact hp.unique hconst

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteCharacterConductor.Construction
