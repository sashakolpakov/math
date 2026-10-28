import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ParameterChoices
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data

/-! # Primes -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Primes.ParameterChoices

noncomputable section

/-! The native completion characters determine distinct conjugate finite
primes. Their distinction follows from the actual split completion map. -/

open _root_.NumberField IsDedekindDomain OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Data
open scoped TensorProduct

theorem ringHom_toZMod_eq_of_ker_eq {R : Type*} [Ring R] (q : ℕ)
    (f g : R →+* ZMod q) (h : RingHom.ker f = RingHom.ker g) : f = g := by
  ext a
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective (f a)
  have ha : a - (z : R) ∈ RingHom.ker f := by
    change f (a - (z : R)) = 0
    rw [map_sub, map_intCast, hz, sub_self]
  rw [h] at ha
  change g (a - (z : R)) = 0 at ha
  rw [map_sub, map_intCast, sub_eq_zero] at ha
  exact hz.symm.trans ha.symm

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)

def nativeResidueCharacter (i : Fin s × Bool) : 𝓞 E →+* ZMod q :=
  PadicInt.toZMod.comp (D.localCharacter i)

def nativeLocalPrime (i : Fin s × Bool) : HeightOneSpectrum (𝓞 E) where
  asIdeal := RingHom.ker (nativeResidueCharacter D i)
  isPrime := RingHom.ker_isPrime _
  ne_bot := by
    intro h
    have hq : (q : 𝓞 E) ∈ RingHom.ker (nativeResidueCharacter D i) := by
      change nativeResidueCharacter D i q = 0
      simp
    rw [h, Ideal.mem_bot] at hq
    exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) hq

theorem nativeLocalPrime_liesOver (i : Fin s × Bool) : (q : 𝓞 E) ∈ (nativeLocalPrime D i).asIdeal := by
  change nativeResidueCharacter D i q = 0
  simp

theorem nativeResidueCharacter_injective (hg : D.IsGoodCompletelySplitPrime) :
    Function.Injective (nativeResidueCharacter D) := by
  intro i j hij
  by_contra hne
  have hcoord (z : ℤ_[q] ⊗[ℤ] 𝓞 E) :
      PadicInt.toZMod (D.localCompletionMap z i) = PadicInt.toZMod (D.localCompletionMap z j) := by
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      change PadicInt.toZMod (a * D.localCharacter i b) =
        PadicInt.toZMod (a * D.localCharacter j b)
      rw [map_mul, map_mul]
      exact congrArg (PadicInt.toZMod a * ·) (RingHom.congr_fun hij b)
    | add x y hx hy =>
      simp only [map_add, Pi.add_apply, hx, hy]
  obtain ⟨z, hz⟩ := hg.1.2 (Pi.single i 1)
  have h := hcoord z
  rw [hz] at h
  simp [Ne.symm hne] at h

theorem nativeLocalPrime_injective (hg : D.IsGoodCompletelySplitPrime) :
    Function.Injective (nativeLocalPrime D) := by
  intro i j hij
  apply nativeResidueCharacter_injective D hg
  apply ringHom_toZMod_eq_of_ker_eq q
  exact congrArg (fun p : HeightOneSpectrum (𝓞 E) => p.asIdeal) hij

theorem nativeLocalPrime_conjugate (hg : D.IsGoodCompletelySplitPrime)
    (v : Fin s) (side : Bool) :
    (nativeLocalPrime D (v, !side)).asIdeal =
      Ideal.map (NumberField.IsCMField.ringOfIntegersComplexConj E).toRingHom
        (nativeLocalPrime D (v, side)).asIdeal := by
  let c := NumberField.IsCMField.ringOfIntegersComplexConj E
  have hc (a : 𝓞 E) : c (c a) = a := by
    apply NumberField.RingOfIntegers.ext
    exact NumberField.IsCMField.complexConj_apply_apply E (a : E)
  apply le_antisymm
  · intro a ha
    apply (Ideal.mem_map_iff_of_surjective c.toRingHom c.surjective).mpr
    refine ⟨c a, ?_, ?_⟩
    · change PadicInt.toZMod (D.localCharacter (v, side) (c a)) = 0
      change PadicInt.toZMod (D.localCharacter (v, !side) a) = 0 at ha
      exact (congrArg PadicInt.toZMod (hg.2.1 v side a)).symm.trans ha
    · exact hc a
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective c.toRingHom c.surjective).mp ha
    change PadicInt.toZMod (D.localCharacter (v, !side) (c b)) = 0
    rw [hg.2.1 v side (c b)]
    change PadicInt.toZMod (D.localCharacter (v, side) (c (c b))) = 0
    rw [hc]
    exact hb

/-- NormOneApproximation now applies to the actual native local characters, with no separate
prime-distinction or conjugate-prime identification premise. -/
theorem exists_native_split_scalar [IsGalois ℚ E] (hg : D.IsGoodCompletelySplitPrime)
    (v : Fin s) (side : Bool) :
    ∃ (r : Eˣ) (M : ℕ), 0 < M ∧
      (r : E) * NumberField.IsCMField.complexConj E (r : E) = 1 ∧
      (∀ i : Fin s × Bool, (nativeLocalPrime D i).valuation E (r : E) =
        if i = (v, side) then WithZero.exp (-(M : ℤ))
        else if i = (v, !side) then WithZero.exp (M : ℤ) else 1) ∧
      (∀ p : HeightOneSpectrum (𝓞 E),
        p ≠ nativeLocalPrime D (v, side) → p ≠ nativeLocalPrime D (v, !side) →
          p.valuation E (r : E) = 1) ∧
      (∀ (S : Finset (HeightOneSpectrum (𝓞 E))) (depth : HeightOneSpectrum (𝓞 E) → ℕ),
        nativeLocalPrime D (v, side) ∉ S → nativeLocalPrime D (v, !side) ∉ S →
        ∃ N : ℕ, 0 < N ∧ ∀ p ∈ S,
          p.valuation E ((r : E) ^ N - 1) ≤ WithZero.exp (-(depth p : ℤ))) := by
  classical
  have hpair : (v, side) ≠ (v, !side) := by
    intro h
    have hs := congrArg Prod.snd h
    cases side <;> simp at hs
  have hsplit : nativeLocalPrime D (v, side) ≠ nativeLocalPrime D (v, !side) :=
    fun h => hpair (nativeLocalPrime_injective D hg h)
  obtain ⟨r, M, hM, hnorm, hleft, hright, hrest, happrox⟩ :=
    NumberTheory.CMField.NormOneApproximation.Construction.exists_norm_one_scalar (E := E) inferInstance
      (nativeLocalPrime D (v, side)) (nativeLocalPrime D (v, !side))
      (nativeLocalPrime_conjugate D hg v side) hsplit
  refine ⟨r, M, hM, hnorm, ?_, hrest, happrox⟩
  intro i
  split_ifs with hi hj
  · subst i
    exact hleft
  · subst i
    exact hright
  · exact hrest _ (fun h => hi (nativeLocalPrime_injective D hg h))
      (fun h => hj (nativeLocalPrime_injective D hg h))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Primes.ParameterChoices
