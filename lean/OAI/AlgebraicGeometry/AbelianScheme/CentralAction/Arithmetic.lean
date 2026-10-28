import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Norm

/-! # Arithmetic -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Arithmetic.Construction

noncomputable section

/-!
Arithmetic principalization for CentralAction. No statement stubs are imported.
The Finiteness hypothesis is exactly its fractional-ideal principalization clause.
The correction a / conjugate(a) * r^m simultaneously fixes the ideal
and the polarization multiplier, without assuming a norm-unit correction.
-/

open _root_.NumberField
open scoped nonZeroDivisors

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

abbrev FI (E : Type*) [Field E] [NumberField E] :=
  FractionalIdeal (𝓞 E)⁰ E

def conjugateIdeal : FI E ≃+* FI E :=
  FractionalIdeal.ringEquivOfRingEquiv E E
    (IsCMField.ringOfIntegersComplexConj E).toRingEquiv

lemma conjugateIdeal_principal (a : E) :
    conjugateIdeal (FractionalIdeal.spanSingleton (𝓞 E)⁰ a) =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ (IsCMField.complexConj E a) := by
  rw [conjugateIdeal, FractionalIdeal.ringEquivOfRingEquiv_spanSingleton]
  congr 1
  have h : IsFractionRing.ringEquivOfRingEquiv
      (K := E) (L := E) (IsCMField.ringOfIntegersComplexConj E).toRingEquiv =
      (IsCMField.complexConj E).toRingEquiv := by
    apply RingEquiv.toRingHom_injective
    apply IsLocalization.ringHom_ext (𝓞 E)⁰
    ext b
    exact IsFractionRing.ringEquivOfRingEquiv_algebraMap
      (IsCMField.ringOfIntegersComplexConj E).toRingEquiv b
  exact congrArg (fun f : E ≃+* E => f a) h

/-- Finiteness, stated as an explicit theorem input rather than an imported theorem. -/
def PrincipalizationInput (E : Type*) [Field E] [NumberField E] : Prop :=
  ∀ (I : FI E), I ≠ 0 → ∃ (m : ℕ) (a : E),
    0 < m ∧ a ≠ 0 ∧ I ^ m = FractionalIdeal.spanSingleton (𝓞 E)⁰ a

/-- Principalization of a polarized fractional ideal, with its scalar norm
made exactly the prescribed rational multiplier. This works for both the
norm-one ideal of T3 and the one-side-per-pair ideal of C0. -/
theorem polarized_principalization
    (hFiniteness : PrincipalizationInput E)
    (I : FI E) (hI : I ≠ 0)
    (r : E) (hr : r ≠ 0) (hrc : IsCMField.complexConj E r = r)
    (hpolarized : I * conjugateIdeal I =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ r) :
    ∃ (m : ℕ) (b : E), 0 < m ∧ b ≠ 0 ∧
      I ^ (2 * m) = FractionalIdeal.spanSingleton (𝓞 E)⁰ b ∧
      b * IsCMField.complexConj E b = r ^ (2 * m) := by
  obtain ⟨m, a, hm, ha, hprincipal⟩ := hFiniteness I hI
  let c := IsCMField.complexConj E
  have hca : c a ≠ 0 := (map_ne_zero c).mpr ha
  let b := a / c a * r ^ m
  have hb : b ≠ 0 := mul_ne_zero (div_ne_zero ha hca) (pow_ne_zero m hr)
  refine ⟨m, b, hm, hb, ?_, ?_⟩
  · have hconj : (conjugateIdeal I) ^ m =
        FractionalIdeal.spanSingleton (𝓞 E)⁰ (c a) := by
      rw [← map_pow, hprincipal, conjugateIdeal_principal]
    have hnorm : I ^ m * (conjugateIdeal I) ^ m =
        FractionalIdeal.spanSingleton (𝓞 E)⁰ (r ^ m) := by
      rw [← mul_pow, hpolarized, FractionalIdeal.spanSingleton_pow]
    have hcI : (conjugateIdeal I) ^ m ≠ 0 :=
      pow_ne_zero m ((map_ne_zero (conjugateIdeal (E := E))).mpr hI)
    apply mul_right_cancel₀ hcI
    calc
      I ^ (2 * m) * conjugateIdeal I ^ m =
          I ^ m * (I ^ m * conjugateIdeal I ^ m) := by
        rw [two_mul, pow_add]
        ac_rfl
      _ = FractionalIdeal.spanSingleton (𝓞 E)⁰ a *
          FractionalIdeal.spanSingleton (𝓞 E)⁰ (r ^ m) := by
        rw [hnorm, hprincipal]
      _ = FractionalIdeal.spanSingleton (𝓞 E)⁰ (a * r ^ m) :=
        FractionalIdeal.spanSingleton_mul_spanSingleton _ _
      _ = FractionalIdeal.spanSingleton (𝓞 E)⁰ b * conjugateIdeal I ^ m := by
        rw [hconj, FractionalIdeal.spanSingleton_mul_spanSingleton]
        congr 1
        dsimp [b]
        field_simp
  · dsimp [b]
    simp only [map_mul, map_div₀, map_pow, hrc]
    change a / c a * r ^ m * (c a / c (c a) * r ^ m) = r ^ (2 * m)
    rw [IsCMField.complexConj_apply_apply]
    rw [two_mul, pow_add]
    field_simp

/-- An integral polarized ideal has a generator of a positive power with
the exact multiplier and trivial image in any prescribed finite level
quotient in which q is invertible. No torsion assertion about a geometric
Hecke action is used in this arithmetic construction. -/
theorem marked_integral_principalization
    (hFiniteness : PrincipalizationInput E)
    (I : FI E) (hI : I ≠ 0) (hIntegral : I ≤ 1)
    (q h : ℕ) (hq : q ≠ 0)
    (hpolarized : I * conjugateIdeal I =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ ((q : E) ^ h))
    {B : Type*} [CommRing B] [Finite B]
    (level : 𝓞 E →+* B) (hqlevel : IsUnit (level (q : 𝓞 E))) :
    ∃ (n : ℕ) (b : 𝓞 E), 0 < n ∧ b ≠ 0 ∧
      I ^ n = FractionalIdeal.spanSingleton (𝓞 E)⁰ (b : E) ∧
      (b : E) * IsCMField.complexConj E (b : E) = (q : E) ^ (h * n) ∧
      level b = 1 := by
  obtain ⟨m, a, hm, ha, hprincipal, hnorm⟩ :=
    polarized_principalization hFiniteness I hI ((q : E) ^ h)
      (pow_ne_zero h (Nat.cast_ne_zero.mpr hq)) (by simp) hpolarized
  have hpowIntegral : I ^ (2 * m) ≤ (1 : FI E) := by
    simpa using pow_le_pow_left' hIntegral (2 * m)
  have haIntegral : a ∈ (1 : FI E) :=
    hpowIntegral (hprincipal ▸ FractionalIdeal.mem_spanSingleton_self (𝓞 E)⁰ a)
  obtain ⟨aInt, haInt⟩ := (FractionalIdeal.mem_one_iff (𝓞 E)⁰).mp haIntegral
  have haInt' : (aInt : E) = a := haInt
  have haInt0 : aInt ≠ 0 := by
    intro hz
    apply ha
    rw [← haInt', hz]
    rfl
  have hnormInt : aInt * IsCMField.ringOfIntegersComplexConj E aInt =
      (q : 𝓞 E) ^ (h * (2 * m)) := by
    apply RingOfIntegers.ext
    change (aInt : E) * IsCMField.complexConj E (aInt : E) = (q : E) ^ (h * (2 * m))
    rw [haInt', pow_mul]
    exact hnorm
  have hunit : IsUnit (level aInt) := by
    apply isUnit_of_mul_isUnit_left (y := level (IsCMField.ringOfIntegersComplexConj E aInt))
    rw [← map_mul, hnormInt, map_pow]
    exact hqlevel.pow _
  obtain ⟨k, hk, horder⟩ :=
    (isOfFinOrder_of_finite hunit.unit).exists_pow_eq_one
  refine ⟨2 * m * k, aInt ^ k, by positivity, pow_ne_zero k haInt0, ?_, ?_, ?_⟩
  · rw [pow_mul, hprincipal, ← haInt', FractionalIdeal.spanSingleton_pow]
    rfl
  · push_cast
    change (aInt : E) ^ k * IsCMField.complexConj E ((aInt : E) ^ k) = _
    rw [map_pow, ← mul_pow, haInt', hnorm, ← pow_mul, ← pow_mul]
  · rw [map_pow, ← hunit.unit_spec]
    exact congrArg Units.val horder

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Arithmetic.Construction
