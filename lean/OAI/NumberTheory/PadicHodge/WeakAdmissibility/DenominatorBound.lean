import OAI.NumberTheory.PadicHodge.WeakAdmissibility.FiniteDeRhamP
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaDividedPowers

/-! # Denominator Bound -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.DenominatorBound

noncomputable section

/-! The actual crystalline envelope has uniformly bounded denominators modulo xi^m. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaKernel OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaQuotients OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRham
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamEmbedding OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamEnvelope OAI.NumberTheory.PadicHodge.WeakAdmissibility.FiniteDeRhamP OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaDividedPowers
variable (p : ℕ) [Fact p.Prime]

theorem thetaDividedPower_finite_zero (m n : ℕ) (hmn : m ≤ n) :
    FiniteDeRhamP.uncompletedToFinite p m (ThetaDividedPowers.thetaDividedPower p n) = 0 := by
  have hz : FiniteDeRhamP.uncompletedToFinite p m
      (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p) (ThetaKernel.thetaGenerator p) ^ n) = 0 := by
    rw [← map_pow, FiniteDeRhamP.uncompletedToFinite_algebraMap, FiniteDeRhamP.integralToFinite_mk]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [DeRhamEmbedding.deRhamIdeal_eq_span, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    change DeRhamEmbedding.xiBInf p ^ m ∣ algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.BInf p) (ThetaKernel.thetaGenerator p ^ n)
    rw [map_pow]
    exact pow_dvd_pow (DeRhamEmbedding.xiBInf p) hmn
  rw [← DeRhamEnvelope.factorial_mul_dividedPower p (ThetaKernel.thetaGenerator p) _ n, map_mul, map_natCast] at hz
  change (n.factorial : FiniteDeRhamP.FiniteDeRham p m) *
    FiniteDeRhamP.uncompletedToFinite p m (ThetaDividedPowers.thetaDividedPower p n) = 0 at hz
  exact (FiniteDeRhamP.factorial_isUnit p m n).mul_left_cancel (hz.trans (mul_zero _).symm)

def boundedSubmodule (m : ℕ) : Submodule (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p) where
  carrier := {x | ∃ r : ThetaQuotients.ThetaPowerQuotient p m,
    FiniteDeRhamP.integralToFinite p m r = (p : FiniteDeRhamP.FiniteDeRham p m) ^ m * FiniteDeRhamP.uncompletedToFinite p m x}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨r, hr⟩ ⟨s, hs⟩
    refine ⟨r + s, ?_⟩
    change FiniteDeRhamP.integralToFinite p m (r + s) =
      (p : FiniteDeRhamP.FiniteDeRham p m) ^ m * FiniteDeRhamP.uncompletedToFinite p m (x + y)
    rw [(FiniteDeRhamP.integralToFinite p m).map_add, hr, hs,
      (FiniteDeRhamP.uncompletedToFinite p m).map_add, mul_add]
  smul_mem' := by
    rintro a x ⟨r, hr⟩
    refine ⟨Ideal.Quotient.mk _ a * r, ?_⟩
    rw [map_mul, hr, Algebra.smul_def, map_mul, FiniteDeRhamP.uncompletedToFinite_algebraMap]
    ring

theorem thetaDividedPower_bounded (m n : ℕ) :
    ThetaDividedPowers.thetaDividedPower p n ∈ boundedSubmodule p m := by
  by_cases hmn : m ≤ n
  · refine ⟨0, ?_⟩
    rw [map_zero, thetaDividedPower_finite_zero p m n hmn, mul_zero]
  · have hnm : n ≤ m := le_of_lt (lt_of_not_ge hmn)
    refine ⟨Ideal.Quotient.mk _ ((p : Logarithm.PeriodRings.AInf p) ^ (m - n) *
      (PeriodInvariants.AdicEstimates.Frobenius.pDividedPowerCoefficient p n * ThetaKernel.thetaGenerator p ^ n)), ?_⟩
    rw [← FiniteDeRhamP.uncompletedToFinite_algebraMap, map_mul, map_pow, map_natCast,
      ← ThetaDividedPowers.thetaDividedPower_integral_mul, map_mul, map_mul, map_pow, map_natCast]
    rw [(FiniteDeRhamP.uncompletedToFinite p m).map_pow, map_natCast,
      ← mul_assoc, ← pow_add, Nat.sub_add_cancel hnm]

/-- Multiplication by p^m puts the whole envelope in A_inf/(xi^m). -/
theorem uncompleted_denominator_bound (m : ℕ) (x : Logarithm.PeriodRings.ACrisUncompleted p) :
    ∃ r : ThetaQuotients.ThetaPowerQuotient p m,
      FiniteDeRhamP.integralToFinite p m r = (p : FiniteDeRhamP.FiniteDeRham p m) ^ m * FiniteDeRhamP.uncompletedToFinite p m x := by
  have hle : Submodule.span (Logarithm.PeriodRings.AInf p) (Set.range (ThetaDividedPowers.thetaDividedPower p)) ≤ boundedSubmodule p m := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact thetaDividedPower_bounded p m n
  exact hle (ThetaDividedPowers.uncompleted_mem_span p x)

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.DenominatorBound
