import OAI.NumberTheory.PadicHodge.PeriodInvariants.Quotient
import OAI.NumberTheory.PadicHodge.PeriodInvariants.PrincipalEnvelope

/-! # Finite Lattices -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteLattices.Period

noncomputable section

/-!
# Integral lattices in the finite de Rham quotients

The integral theta quotients embed in their p-localizations. A single factorial
clears the denominators of the entire divided-power envelope in each quotient.
-/

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing OAI.NumberTheory.PadicHodge.PeriodInvariants.ThetaKernel OAI.NumberTheory.PadicHodge.PeriodInvariants.Nontriviality OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicSeparation
  PeriodInvariants.Quotient PrincipalEnvelope

variable (p : ℕ) [Fact p.Prime]

abbrev IntegralQuotient (N : ℕ) := PeriodRing.Ainf p ⧸ Ideal.span {ThetaKernel.xi p ^ N}

abbrev RationalQuotient (N : ℕ) :=
  Nontriviality.Binf p ⧸ (Ideal.span {ThetaKernel.xi p ^ N}).map (algebraMap (PeriodRing.Ainf p) (Nontriviality.Binf p))

instance integralQuotient_complete (N : ℕ) :
    IsAdicComplete (Ideal.span {(p : IntegralQuotient p N)}) (IntegralQuotient p N) :=
  PeriodInvariants.Quotient.thetaPowerQuotient_complete p N

instance rationalQuotient_localization (N : ℕ) :
    IsLocalization (Submonoid.powers (p : IntegralQuotient p N)) (RationalQuotient p N) := by
  have h : IsLocalization
      (Algebra.algebraMapSubmonoid (IntegralQuotient p N) (Submonoid.powers (p : PeriodRing.Ainf p)))
      (RationalQuotient p N) := inferInstance
  simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers, map_natCast] using h

theorem integralQuotient_p_cancel (N n : ℕ) (x : IntegralQuotient p N)
    (hx : (p : IntegralQuotient p N) ^ n * x = 0) : x = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hm : ThetaKernel.xi p ^ N ∣ (p : PeriodRing.Ainf p) ^ n * a := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul, map_pow, map_natCast] using hx
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.mem_span_singleton.mpr (AdicSeparation.xi_pow_dvd_of_p_pow_mul p N n a hm)

/-- The integral lattice embeds faithfully in each rational finite quotient. -/
theorem integralQuotient_injective (N : ℕ) :
    Function.Injective (algebraMap (IntegralQuotient p N) (RationalQuotient p N)) := by
  apply IsLocalization.injective (M := Submonoid.powers (p : IntegralQuotient p N))
    (RationalQuotient p N)
  intro a ha
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff a (p : IntegralQuotient p N)).mp ha
  rw [mem_nonZeroDivisors_iff_left]
  intro x hx
  exact integralQuotient_p_cancel p N n x hx

def envelopeProjection (N : ℕ) : PeriodRing.AcrisZero p →ₐ[PeriodRing.Ainf p] RationalQuotient p N :=
  { (Ideal.Quotient.mk _).comp (Nontriviality.acrisZeroToBinf p) with
    commutes' a := by
      change Ideal.Quotient.mk _ (Nontriviality.acrisZeroToBinf p (algebraMap (PeriodRing.Ainf p) (PeriodRing.AcrisZero p) a)) = _
      rw [Nontriviality.acrisZeroToBinf_algebraMap]
      rfl }

theorem factorial_unit (N n : ℕ) : IsUnit (n.factorial : RationalQuotient p N) := by
  have h : IsUnit (n.factorial : ℚ_[p]) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
  have hh := h.map ((Ideal.Quotient.mk _).comp (Nontriviality.padicToBinf p) : ℚ_[p] →+* RationalQuotient p N)
  simpa only [map_natCast] using hh

theorem projection_factorial_dividedPower (N n : ℕ) :
    (n.factorial : RationalQuotient p N) * envelopeProjection p N (PrincipalEnvelope.xiDividedPower p n) =
      algebraMap (PeriodRing.Ainf p) (RationalQuotient p N) (ThetaKernel.xi p) ^ n := by
  have h := congrArg (envelopeProjection p N) (PeriodRing.factorial_mul_dividedPower p n (PrincipalEnvelope.xiKernel p))
  simpa only [map_mul, map_natCast, map_pow, AlgHom.commutes, PrincipalEnvelope.xiDividedPower, PrincipalEnvelope.xiKernel] using h

theorem projection_dividedPower_vanishes (N n : ℕ) (hn : N ≤ n) :
    envelopeProjection p N (PrincipalEnvelope.xiDividedPower p n) = 0 := by
  apply (factorial_unit p N n).mul_left_cancel
  rw [mul_zero, projection_factorial_dividedPower]
  have hm : ThetaKernel.xi p ^ n ∈ Ideal.span {ThetaKernel.xi p ^ N} :=
    Ideal.mem_span_singleton.mpr (pow_dvd_pow (ThetaKernel.xi p) hn)
  have hmap := Ideal.mem_map_of_mem (algebraMap (PeriodRing.Ainf p) (Nontriviality.Binf p)) hm
  have hzero := Ideal.Quotient.eq_zero_iff_mem.mpr hmap
  change Ideal.Quotient.mk _ (algebraMap (PeriodRing.Ainf p) (Nontriviality.Binf p) (ThetaKernel.xi p ^ n)) = 0 at hzero
  rw [IsScalarTower.algebraMap_apply (PeriodRing.Ainf p) (Nontriviality.Binf p) (RationalQuotient p N)]
  rw [Ideal.Quotient.algebraMap_eq]
  simpa only [map_pow] using hzero

theorem factorial_projection_dividedPower_integral (N n : ℕ) :
    ∃ a : PeriodRing.Ainf p, algebraMap (PeriodRing.Ainf p) (RationalQuotient p N) a =
      (N.factorial : RationalQuotient p N) * envelopeProjection p N (PrincipalEnvelope.xiDividedPower p n) := by
  by_cases hn : N ≤ n
  · exact ⟨0, by rw [map_zero, projection_dividedPower_vanishes p N n hn, mul_zero]⟩
  · obtain ⟨k, hk⟩ := Nat.factorial_dvd_factorial (show n ≤ N by omega)
    refine ⟨(k : PeriodRing.Ainf p) * ThetaKernel.xi p ^ n, ?_⟩
    rw [map_mul, map_natCast, map_pow, hk, Nat.cast_mul]
    rw [mul_right_comm (n.factorial : RationalQuotient p N),
      projection_factorial_dividedPower]
    ring

/-- One denominator bound holds for every element of the uncompleted envelope. -/
theorem factorial_projection_integral (N : ℕ) (x : PeriodRing.AcrisZero p) :
    ∃ a : PeriodRing.Ainf p, algebraMap (PeriodRing.Ainf p) (RationalQuotient p N) a =
      (N.factorial : RationalQuotient p N) * envelopeProjection p N x := by
  have hx : x ∈ Submodule.span (PeriodRing.Ainf p) (Set.range (PrincipalEnvelope.xiDividedPower p)) := by
    change x ∈ PrincipalEnvelope.dividedPowerSpan p
    rw [PrincipalEnvelope.dividedPowerSpan_eq_top]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨n, rfl⟩ := hy
    exact factorial_projection_dividedPower_integral p N n
  | zero => exact ⟨0, by rw [map_zero, map_zero, mul_zero]⟩
  | add y z hy hz ihy ihz =>
    obtain ⟨a, ha⟩ := ihy
    obtain ⟨b, hb⟩ := ihz
    exact ⟨a + b, by rw [map_add, ha, hb, map_add, mul_add]⟩
  | smul r y hy ih =>
    obtain ⟨a, ha⟩ := ih
    refine ⟨r * a, ?_⟩
    rw [Algebra.smul_def r y, map_mul, map_mul, AlgHom.commutes, ha]
    ring

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteLattices.Period
