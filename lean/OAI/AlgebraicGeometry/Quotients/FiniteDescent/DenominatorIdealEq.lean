import Mathlib.RingTheory.Localization.NumDen
import Mathlib.RingTheory.Ideal.Span

/-! # Denominator Ideal Eq -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.DenominatorIdealEq.Construction.DenominatorIdeal

noncomputable section

/-! The ideal of denominators of a rational function and its local generator. -/

variable {R F : Type*} [CommRing R] [Field F] [Algebra R F]

def ideal (x : F) : Ideal R where
  carrier := {r | ∃ s : R, algebraMap R F r * x = algebraMap R F s}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c + d, by rw [map_add, add_mul, hc, hd, map_add]⟩
  smul_mem' := by
    rintro a b ⟨c, hc⟩
    exact ⟨a * c, by rw [smul_eq_mul, map_mul, mul_assoc, hc, map_mul]⟩

theorem mem_iff (x : F) (r : R) :
    r ∈ ideal x ↔ ∃ s : R, algebraMap R F r * x = algebraMap R F s := Iff.rfl

variable [IsDomain R] [IsFractionRing R F]

omit [IsDomain R] in
theorem mem_iff_dvd (a b r : R) (hb : b ≠ 0) {x : F}
    (hx : x = algebraMap R F a / algebraMap R F b) :
    r ∈ ideal x ↔ b ∣ a * r := by
  have hb' : algebraMap R F b ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R F).ne hb
  rw [mem_iff, hx]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    apply IsFractionRing.injective R F
    rw [map_mul, map_mul]
    have h := (div_eq_iff hb').mp (show algebraMap R F r * algebraMap R F a /
      algebraMap R F b = algebraMap R F s by rwa [← mul_div_assoc] at hs)
    simpa [mul_comm] using h
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    rw [← mul_div_assoc]
    apply (div_eq_iff hb').mpr
    have h := congrArg (algebraMap R F) hs
    simpa [map_mul, mul_comm] using h

omit [IsDomain R] in
theorem eq_span_of_reduced [DecompositionMonoid R] (a b : R) (hb : b ≠ 0)
    (hab : IsRelPrime a b) {x : F}
    (hx : x = algebraMap R F a / algebraMap R F b) : ideal x = Ideal.span {b} := by
  ext r
  rw [mem_iff_dvd a b r hb hx, Ideal.mem_span_singleton]
  exact ⟨fun h => hab.symm.dvd_of_dvd_mul_left h, fun h => h.mul_left a⟩

theorem isPrincipal [UniqueFactorizationMonoid R] (x : F) : (ideal (R := R) x).IsPrincipal := by
  refine ⟨(IsFractionRing.den R x : R), ?_⟩
  exact eq_span_of_reduced (IsFractionRing.num R x) _
    (nonZeroDivisors.ne_zero (IsFractionRing.den R x).2)
    (IsFractionRing.num_den_reduced R x) (IsFractionRing.mk'_num_den' R x).symm

theorem ne_bot (x : F) : ideal (R := R) x ≠ ⊥ := by
  obtain ⟨a, b, hab⟩ := IsLocalization.exists_mk'_eq (nonZeroDivisors R) x
  intro h
  have hm : (b : R) ∈ ideal x := ⟨a, by
    rw [← hab, IsLocalization.mk'_spec']⟩
  rw [h, Ideal.mem_bot] at hm
  exact nonZeroDivisors.ne_zero b.2 hm

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.DenominatorIdealEq.Construction.DenominatorIdeal
