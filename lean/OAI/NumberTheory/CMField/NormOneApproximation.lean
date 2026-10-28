import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Norm
import OAI.NumberTheory.ClassGroup.Finiteness

/-! # Norm One Approximation -/

namespace OAI.NumberTheory.CMField.NormOneApproximation.Construction

noncomputable section

/-!
Proof of NormOneApproximation, retaining the conditional theorem for existing consumers.
The final entrypoint `exists_norm_one_scalar_unconditional` supplies the
named input `hFiniteness_classGroup_finite` from the proved Finiteness declaration.
This is the first proposition of Statements/Finiteness.lean, specialized to E. Its
fractional-ideal principalization assertion is redundant here. CMPoints, TensorDecomposition,
and ElementaryDivisors are unnecessary for this arithmetic result with the two distinct
conjugate primes already specified. No statement stub is imported.

As in the specification, multiplicative valuation exp(-m) means additive
order m. The local approximation clause concerns further positive powers.
The manuscript's scalar assertion is in
docs/hodge_cm_claimed_result_labeled.tex, lemma:norm-one-scalar (lines 353-361).
-/

open _root_.NumberField IsDedekindDomain
open scoped nonZeroDivisors

variable {E : Type*} [Field E] [NumberField E]

lemma principal_prime_power
    (hFiniteness_classGroup_finite : Finite (ClassGroup (𝓞 E)))
    (w : HeightOneSpectrum (𝓞 E)) :
    ∃ (M : ℕ) (a : 𝓞 E), 0 < M ∧ a ≠ 0 ∧
      w.asIdeal ^ M = Ideal.span {a} := by
  let := hFiniteness_classGroup_finite
  let I : (Ideal (𝓞 E))⁰ := ⟨w.asIdeal, mem_nonZeroDivisors_of_ne_zero w.ne_bot⟩
  obtain ⟨M, hM, heq⟩ := (isOfFinOrder_of_finite (ClassGroup.mk0 I)).exists_pow_eq_one
  have hprincipal : (w.asIdeal ^ M).IsPrincipal := by
    apply (ClassGroup.mk0_eq_one_iff (pow_mem I.property M)).mp
    simpa only [I, ← map_pow, SubmonoidClass.mk_pow] using heq
  obtain ⟨a, ha⟩ := hprincipal.principal
  refine ⟨M, a, hM, ?_, ha⟩
  intro hzero
  have hpow : w.asIdeal ^ M ≠ 0 := pow_ne_zero M w.prime.ne_zero
  apply hpow
  simpa [hzero] using ha

lemma valuation_generator_self
    (w : HeightOneSpectrum (𝓞 E)) (M : ℕ) (a : 𝓞 E)
    (ha : a ≠ 0) (hspan : w.asIdeal ^ M = Ideal.span {a}) :
    w.intValuation a = WithZero.exp (-(M : ℤ)) := by
  rw [w.intValuation_eq_exp_neg_multiplicity ha, ← hspan,
    multiplicity_pow_self_of_prime w.prime]

lemma valuation_generator_other
    (w p : HeightOneSpectrum (𝓞 E)) (M : ℕ) (a : 𝓞 E)
    (hspan : w.asIdeal ^ M = Ideal.span {a}) (hp : p ≠ w) :
    p.intValuation a = 1 := by
  apply p.intValuation_eq_one_iff.mpr
  intro hmem
  have hdvd : p.asIdeal ∣ w.asIdeal ^ M := by
    rw [hspan, Ideal.dvd_span_singleton]
    exact hmem
  have hle : w.asIdeal ≤ p.asIdeal :=
    Ideal.dvd_iff_le.mp (p.prime.dvd_of_dvd_pow hdvd)
  apply hp
  apply HeightOneSpectrum.asIdeal_injective
  exact ((w.isMaximal).eq_of_le (p.isPrime.ne_top) hle).symm

/-- Simultaneous congruences for two integral elements which are units
at every prime in S, using the finite product of residue-unit groups. -/
lemma simultaneous_power_congruence
    (S : Finset (HeightOneSpectrum (𝓞 E)))
    (depth : HeightOneSpectrum (𝓞 E) → ℕ)
    (a b : 𝓞 E)
    (ha : ∀ p ∈ S, a ∉ p.asIdeal)
    (hb : ∀ p ∈ S, b ∉ p.asIdeal) :
    ∃ N : ℕ, 0 < N ∧ ∀ p ∈ S,
      a ^ N - b ^ N ∈ p.asIdeal ^ depth p := by
  classical
  let Q (p : S) := 𝓞 E ⧸ p.val.asIdeal ^ depth p.val
  let (p : S) : Finite (Q p) :=
    Ring.HasFiniteQuotients.finiteQuotient
      (pow_ne_zero _ p.val.prime.ne_zero)
  let G := (p : S) → (Q p)ˣ
  let ua : G := fun p =>
    (Ideal.Quotient.isUnit_mk_pow_of_notMem p.val.asIdeal
      (ha p.val p.property)).unit
  let ub : G := fun p =>
    (Ideal.Quotient.isUnit_mk_pow_of_notMem p.val.asIdeal
      (hb p.val p.property)).unit
  have hPow (g : G) (p : S) : g p ^ Nat.card G = 1 :=
    congrFun (pow_card_eq_one' (x := g)) p
  refine ⟨Nat.card G, Nat.card_pos, ?_⟩
  intro p hp
  have hea := congrArg Units.val (hPow ua ⟨p, hp⟩)
  have heb := congrArg Units.val (hPow ub ⟨p, hp⟩)
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simp only [map_sub, map_pow]
  have hea' : Ideal.Quotient.mk (p.asIdeal ^ depth p) a ^ Nat.card G = 1 := by
    simpa only [Pi.pow_apply, Units.val_pow_eq_pow_val, Pi.one_apply,
      Units.val_one, ua, IsUnit.unit_spec] using hea
  have heb' : Ideal.Quotient.mk (p.asIdeal ^ depth p) b ^ Nat.card G = 1 := by
    simpa only [Pi.pow_apply, Units.val_pow_eq_pow_val, Pi.one_apply,
      Units.val_one, ub, IsUnit.unit_spec] using heb
  rw [hea', heb', sub_self]

/-- The integral congruence becomes a valuation bound on the ratio. -/
lemma ratio_powers_approximate_one
    (S : Finset (HeightOneSpectrum (𝓞 E)))
    (depth : HeightOneSpectrum (𝓞 E) → ℕ)
    (a b : 𝓞 E) (hb0 : b ≠ 0)
    (ha : ∀ p ∈ S, a ∉ p.asIdeal)
    (hb : ∀ p ∈ S, b ∉ p.asIdeal) :
    ∃ N : ℕ, 0 < N ∧ ∀ p ∈ S,
      p.valuation E (((a : E) / (b : E)) ^ N - 1) ≤
        WithZero.exp (-(depth p : ℤ)) := by
  obtain ⟨N, hN, hcong⟩ := simultaneous_power_congruence S depth a b ha hb
  refine ⟨N, hN, ?_⟩
  intro p hp
  have hbE : (b : E) ≠ 0 := by exact_mod_cast hb0
  have hratio : ((a : E) / (b : E)) ^ N - 1 =
      ((a ^ N - b ^ N : 𝓞 E) : E) / (b : E) ^ N := by
    push_cast
    rw [div_pow]
    field_simp
  have hbval : p.valuation E (b : E) = 1 :=
    (p.valuation_eq_one_iff_notMem).mpr (hb p hp)
  rw [hratio, map_div₀, map_pow, hbval, one_pow, div_one,
    p.valuation_of_algebraMap]
  exact (p.intValuation_le_pow_iff_mem _ _).mpr (hcong p hp)

/-- NormOneApproximation, conditional on the finiteness assertion of Finiteness. -/
theorem exists_norm_one_scalar
    [Algebra ℚ E] [NumberField.IsCMField E] [IsGalois ℚ E]
    (hFiniteness_classGroup_finite : Finite (ClassGroup (𝓞 E)))
    (w wbar : HeightOneSpectrum (𝓞 E))
    (hconj : wbar.asIdeal =
      Ideal.map
        (NumberField.IsCMField.ringOfIntegersComplexConj E).toRingHom
        w.asIdeal)
    (hsplit : w ≠ wbar) :
    ∃ (r : Eˣ) (M : ℕ),
      0 < M ∧
      (r : E) * NumberField.IsCMField.complexConj E (r : E) = 1 ∧
      w.valuation E (r : E) = WithZero.exp (-(M : ℤ)) ∧
      wbar.valuation E (r : E) = WithZero.exp (M : ℤ) ∧
      (∀ p : HeightOneSpectrum (𝓞 E),
        p ≠ w → p ≠ wbar → p.valuation E (r : E) = 1) ∧
      (∀ (S : Finset (HeightOneSpectrum (𝓞 E)))
          (depth : HeightOneSpectrum (𝓞 E) → ℕ),
        w ∉ S → wbar ∉ S →
        ∃ N : ℕ, 0 < N ∧
          ∀ p ∈ S,
            p.valuation E ((r : E) ^ N - 1) ≤
              WithZero.exp (-(depth p : ℤ))) := by
  obtain ⟨M, a, hM, ha, hspan⟩ := principal_prime_power hFiniteness_classGroup_finite w
  let b := NumberField.IsCMField.ringOfIntegersComplexConj E a
  have hb : b ≠ 0 := by
    intro hz
    apply ha
    apply (NumberField.IsCMField.ringOfIntegersComplexConj E).injective
    simpa only [map_zero] using hz
  have hspanb : wbar.asIdeal ^ M = Ideal.span {b} := by
    rw [hconj, ← Ideal.map_pow, hspan, Ideal.map_span, Set.image_singleton]
    rfl
  have haE : (a : E) ≠ 0 := by exact_mod_cast ha
  have hbE : (b : E) ≠ 0 := by exact_mod_cast hb
  let r : Eˣ := Units.mk0 ((a : E) / (b : E)) (div_ne_zero haE hbE)
  have hca : NumberField.IsCMField.complexConj E (a : E) = (b : E) := rfl
  have hcb : NumberField.IsCMField.complexConj E (b : E) = (a : E) := by
    rw [← hca, NumberField.IsCMField.complexConj_apply_apply]
  have hwa := valuation_generator_self w M a ha hspan
  have hwb := valuation_generator_other wbar w M b hspanb hsplit
  have hwbara := valuation_generator_other w wbar M a hspan (Ne.symm hsplit)
  have hwbarb := valuation_generator_self wbar M b hb hspanb
  refine ⟨r, M, hM, ?_, ?_, ?_, ?_, ?_⟩
  · change (a : E) / (b : E) *
      NumberField.IsCMField.complexConj E ((a : E) / (b : E)) = 1
    rw [map_div₀, hca, hcb]
    field_simp
  · change w.valuation E ((a : E) / (b : E)) = _
    rw [map_div₀, w.valuation_of_algebraMap, w.valuation_of_algebraMap,
      hwa, hwb, div_one]
  · change wbar.valuation E ((a : E) / (b : E)) = _
    rw [map_div₀, wbar.valuation_of_algebraMap, wbar.valuation_of_algebraMap,
      hwbara, hwbarb, one_div, WithZero.exp_neg, inv_inv]
  · intro p hpw hpwbar
    change p.valuation E ((a : E) / (b : E)) = 1
    rw [map_div₀, p.valuation_of_algebraMap, p.valuation_of_algebraMap,
      valuation_generator_other w p M a hspan hpw,
      valuation_generator_other wbar p M b hspanb hpwbar, div_one]
  · intro S depth hwS hwbarS
    apply ratio_powers_approximate_one S depth a b hb
    · intro p hp
      apply p.intValuation_eq_one_iff.mp
      apply valuation_generator_other w p M a hspan
      rintro rfl
      exact hwS hp
    · intro p hp
      apply p.intValuation_eq_one_iff.mp
      apply valuation_generator_other wbar p M b hspanb
      rintro rfl
      exact hwbarS hp

theorem exists_norm_one_scalar_unconditional
    [Algebra ℚ E] [NumberField.IsCMField E] [IsGalois ℚ E]
    (w wbar : HeightOneSpectrum (𝓞 E))
    (hconj : wbar.asIdeal =
      Ideal.map
        (NumberField.IsCMField.ringOfIntegersComplexConj E).toRingHom
        w.asIdeal)
    (hsplit : w ≠ wbar) :
    ∃ (r : Eˣ) (M : ℕ),
      0 < M ∧
      (r : E) * NumberField.IsCMField.complexConj E (r : E) = 1 ∧
      w.valuation E (r : E) = WithZero.exp (-(M : ℤ)) ∧
      wbar.valuation E (r : E) = WithZero.exp (M : ℤ) ∧
      (∀ p : HeightOneSpectrum (𝓞 E),
        p ≠ w → p ≠ wbar → p.valuation E (r : E) = 1) ∧
      (∀ (S : Finset (HeightOneSpectrum (𝓞 E)))
          (depth : HeightOneSpectrum (𝓞 E) → ℕ),
        w ∉ S → wbar ∉ S →
        ∃ N : ℕ, 0 < N ∧
          ∀ p ∈ S,
            p.valuation E ((r : E) ^ N - 1) ≤
              WithZero.exp (-(depth p : ℤ))) := by
  exact exists_norm_one_scalar
    (OAI.NumberTheory.ClassGroup.Finiteness.classGroup_finite E) w wbar hconj hsplit

end

end OAI.NumberTheory.CMField.NormOneApproximation.Construction
