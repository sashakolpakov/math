import Mathlib.NumberTheory.Ostrowski
import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteCompletionNorm

/-! # Finite Norm Padic Comparison -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FiniteNormPadicComparison.Realization

noncomputable section

section

/-! Restrict a finite-completion norm to the rationals. -/

open scoped Classical
open IsDedekindDomain _root_.NumberField

def rationalNormAbsoluteValue (K : Type*) [NormedField K] [Algebra ℚ K] : AbsoluteValue ℚ ℝ where
  toFun x := ‖algebraMap ℚ K x‖
  map_mul' x y := by rw [map_mul, norm_mul]
  nonneg' x := norm_nonneg _
  eq_zero' x := by
    rw [norm_eq_zero]
    exact ⟨fun h => (algebraMap ℚ K).injective (h.trans (map_zero _).symm),
      fun h => by rw [h, map_zero]⟩
  add_le' x y := by rw [map_add]; exact norm_add_le _ _

theorem rational_finite_norm_nat_le_one (E : Type*) [Field E] [NumberField E] [Algebra ℚ E]
    (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    rationalNormAbsoluteValue (w.adicCompletion E) n ≤ 1 := by
  have h := FinitePlace.norm_le_one (K := E) w (n : 𝓞 E)
  change ‖algebraMap ℚ (w.adicCompletion E) (n : ℚ)‖ ≤ 1
  simpa only [map_natCast] using h

theorem rational_finite_norm_prime_lt_one (E : Type*) [Field E] [NumberField E] [Algebra ℚ E]
    (w : HeightOneSpectrum (𝓞 E)) (p : ℕ) (hp : (p : 𝓞 E) ∈ w.asIdeal) :
    rationalNormAbsoluteValue (w.adicCompletion E) p < 1 := by
  have h := (FinitePlace.norm_lt_one_iff_mem (K := E) w (p : 𝓞 E)).mpr hp
  change ‖algebraMap ℚ (w.adicCompletion E) (p : ℚ)‖ < 1
  simpa only [map_natCast] using h

end

/-! A finite-completion norm restricts to a positive power of the corresponding p-adic norm. -/

open scoped Classical
open IsDedekindDomain _root_.NumberField

theorem rational_padic_absoluteValue (p : ℕ) [Fact p.Prime] (x : ℚ) :
    Rat.AbsoluteValue.padic p x = ‖(x : ℚ_[p])‖ := (Padic.eq_padicNorm x).symm

theorem finite_norm_restriction_padic_equiv
    (E : Type*) [Field E] [NumberField E] [Algebra ℚ E] (w : HeightOneSpectrum (𝓞 E))
    (p : ℕ) [Fact p.Prime] (hpw : (p : 𝓞 E) ∈ w.asIdeal) :
    (rationalNormAbsoluteValue (w.adicCompletion E)).IsEquiv (Rat.AbsoluteValue.padic p) := by
  let f := rationalNormAbsoluteValue (w.adicCompletion E)
  have hfp : f p < 1 := rational_finite_norm_prime_lt_one E w p hpw
  have hf : f.IsNontrivial := ⟨(p : ℚ), by exact_mod_cast (Fact.out : p.Prime).ne_zero, hfp.ne⟩
  obtain ⟨l, ⟨hl, he⟩, _⟩ := Rat.AbsoluteValue.equiv_padic_of_bounded hf
    (rational_finite_norm_nat_le_one E w)
  let : Fact l.Prime := hl
  have hlp : ‖(p : ℚ_[l])‖ < 1 := by
    have h := he.lt_one_iff.mp hfp
    simpa only [rational_padic_absoluteValue, Rat.cast_natCast] using h
  have hd : l ∣ p := Padic.norm_natCast_lt_one_iff.mp hlp
  have hlp' : l = p := ((Nat.dvd_prime (Fact.out : p.Prime)).mp hd).resolve_left hl.out.ne_one
  subst l
  exact he

theorem finite_norm_padic_rpow
    (E : Type*) [Field E] [NumberField E] [Algebra ℚ E] (w : HeightOneSpectrum (𝓞 E))
    (p : ℕ) [Fact p.Prime] (hpw : (p : 𝓞 E) ∈ w.asIdeal) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℚ,
      ‖algebraMap ℚ (w.adicCompletion E) x‖ ^ c = ‖(x : ℚ_[p])‖ := by
  obtain ⟨c, hc, he⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp
    (finite_norm_restriction_padic_equiv E w p hpw)
  refine ⟨c, hc, ?_⟩
  intro x
  exact (congrFun he x).trans (rational_padic_absoluteValue p x)

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FiniteNormPadicComparison.Realization
