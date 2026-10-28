import OAI.NumberTheory.PadicHodge.PeriodInvariants.DeRhamLogarithm
import OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicEstimates

/-! # Nontriviality T -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.NontrivialityT

noncomputable section

/-!
# Nontriviality after inverting the cyclotomic period

The period map sends each logarithm to its nonzero argument times a unit.
Consequently every power of t is nonzero, and B_cris is nontrivial.
-/

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing OAI.NumberTheory.PadicHodge.PeriodInvariants.Nontriviality OAI.NumberTheory.PadicHodge.PeriodInvariants.DeRhamStructure OAI.NumberTheory.PadicHodge.PeriodInvariants.DeRhamLogarithm.Comparison
  DeRhamLogarithm DeRhamLogarithm.Finite FiniteComparison AdicEstimates

variable (p : ℕ) [Fact p.Prime]

theorem nativeFiniteComparison_pdLog (x : RingHom.ker (PeriodRing.theta p)) (N : ℕ) :
    DeRhamLogarithm.Comparison.nativeFiniteComparison p N (PeriodRing.pdLog p x) =
      Ideal.Quotient.mk ((RingHom.ker (DeRhamStructure.nativeTheta p)) ^ N)
        (Nontriviality.acrisZeroToBinf p (DeRhamLogarithm.Finite.truncatedLog p x N)) := by
  change Ideal.quotEquivOfEq (DeRhamLogarithm.Comparison.rationalIdeal_eq_native p N) (FiniteComparison.acrisToFiniteQuotient p N (PeriodRing.pdLog p x)) = _
  rw [DeRhamLogarithm.Finite.acrisToFiniteQuotient_pdLog]
  exact Ideal.quotEquivOfEq_mk (DeRhamLogarithm.Comparison.rationalIdeal_eq_native p N) (Nontriviality.acrisZeroToBinf p (DeRhamLogarithm.Finite.truncatedLog p x N))

/-- In the native de Rham completion, the logarithm is its argument times a unit. -/
theorem deRham_pdLog_factor (x : RingHom.ker (PeriodRing.theta p)) :
    (DeRhamLogarithm.Comparison.acrisToDeRhamPlus p (PeriodRing.pdLog p x) : AdicCompletion (RingHom.ker (DeRhamStructure.nativeTheta p)) (Nontriviality.Binf p)) =
      AdicCompletion.of (RingHom.ker (DeRhamStructure.nativeTheta p)) (Nontriviality.Binf p)
        (algebraMap (PeriodRing.Ainf p) (Nontriviality.Binf p) (x : PeriodRing.Ainf p)) * DeRhamLogarithm.deRhamLogUnit p x := by
  apply AdicCompletion.ext_evalₐ
  intro N
  have hprod : AdicCompletion.evalₐ (RingHom.ker (DeRhamStructure.nativeTheta p)) N
      (AdicCompletion.of (RingHom.ker (DeRhamStructure.nativeTheta p)) (Nontriviality.Binf p)
        (algebraMap (PeriodRing.Ainf p) (Nontriviality.Binf p) (x : PeriodRing.Ainf p)) * DeRhamLogarithm.deRhamLogUnit p x) =
      Ideal.Quotient.mk ((RingHom.ker (DeRhamStructure.nativeTheta p)) ^ N)
        (algebraMap (PeriodRing.Ainf p) (Nontriviality.Binf p) (x : PeriodRing.Ainf p) * DeRhamLogarithm.logUnitPartialSum p x N) := by
    rw [map_mul, AdicCompletion.evalₐ_of, DeRhamLogarithm.deRhamLogUnit_eval, map_mul]
  exact (DeRhamLogarithm.Comparison.acrisToDeRhamPlus_eval p N (PeriodRing.pdLog p x)).trans
    ((nativeFiniteComparison_pdLog p x N).trans
      ((congrArg (Ideal.Quotient.mk ((RingHom.ker (DeRhamStructure.nativeTheta p)) ^ N))
        (DeRhamLogarithm.truncatedLog_factor p x N)).trans hprod.symm))

/-- No positive or zero power of the logarithm of a nonzero kernel element vanishes. -/
theorem pdLog_pow_ne_zero (x : RingHom.ker (PeriodRing.theta p)) (hx : (x : PeriodRing.Ainf p) ≠ 0) (n : ℕ) :
    PeriodRing.pdLog p x ^ n ≠ 0 := by
  intro h
  have hd := congrArg (DeRhamLogarithm.Comparison.acrisToDeRhamPlus p) h
  rw [map_pow, map_zero] at hd
  have hd' :
      AdicCompletion.of (RingHom.ker (DeRhamStructure.nativeTheta p)) (Nontriviality.Binf p)
        (algebraMap (PeriodRing.Ainf p) (Nontriviality.Binf p) (x : PeriodRing.Ainf p)) ^ n * DeRhamLogarithm.deRhamLogUnit p x ^ n = 0 :=
    (mul_pow _ _ n).symm.trans
      ((congrArg (fun z : AdicCompletion (RingHom.ker (DeRhamStructure.nativeTheta p)) (Nontriviality.Binf p) => z ^ n)
        (deRham_pdLog_factor p x)).symm.trans hd)
  have harg : AdicCompletion.of (RingHom.ker (DeRhamStructure.nativeTheta p)) (Nontriviality.Binf p)
      (algebraMap (PeriodRing.Ainf p) (Nontriviality.Binf p) (x : PeriodRing.Ainf p)) ^ n = 0 := by
    apply ((DeRhamLogarithm.deRhamLogUnit_isUnit p x).pow n).mul_right_cancel
    rw [zero_mul]
    exact hd'
  have he : algebraMap (PeriodRing.Ainf p) (Nontriviality.Binf p) ((x : PeriodRing.Ainf p) ^ n) = 0 := by
    let i : Nontriviality.Binf p →+* AdicCompletion (RingHom.ker (DeRhamStructure.nativeTheta p)) (Nontriviality.Binf p) :=
      algebraMap (Nontriviality.Binf p) _
    have hi : Function.Injective i := AdicCompletion.of_injective _ _
    apply hi
    rw [map_zero, map_pow, map_pow]
    exact harg
  have he' : (x : PeriodRing.Ainf p) ^ n = 0 :=
    Nontriviality.binf_algebraMap_injective p (he.trans (map_zero _).symm)
  exact pow_ne_zero n hx he'

theorem t_pow_ne_zero (n : ℕ) : PeriodRing.t p ^ n ≠ 0 :=
  pdLog_pow_ne_zero p (PeriodRing.cyclotomicKernelElement p) (PeriodRing.cyclotomicKernelElement_ne_zero p) n

theorem bcrisPlus_t_pow_ne_zero (n : ℕ) :
    algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p) (PeriodRing.t p) ^ n ≠ 0 := by
  intro h
  have he : PeriodRing.t p ^ n = 0 := AdicEstimates.acris_to_bcrisPlus_injective p (by rw [map_pow, h, map_zero])
  exact t_pow_ne_zero p n he

/-- Inverting the actual cyclotomic logarithm does not collapse the crystalline ring. -/
instance bcris_nontrivial : Nontrivial (PeriodRing.Bcris p) := by
  apply nontrivial_of_ne (0 : PeriodRing.Bcris p) 1
  intro h
  have he : algebraMap (PeriodRing.BcrisPlus p) (PeriodRing.Bcris p) 0 = algebraMap (PeriodRing.BcrisPlus p) (PeriodRing.Bcris p) 1 := by
    simpa only [map_zero, map_one] using h
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists
    (Submonoid.powers (algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p) (PeriodRing.t p))) (PeriodRing.Bcris p)).mp he
  have hz : (c : PeriodRing.BcrisPlus p) = 0 := by simpa only [mul_zero, mul_one] using hc.symm
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (c : PeriodRing.BcrisPlus p)
    (algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p) (PeriodRing.t p))).mp c.property
  exact bcrisPlus_t_pow_ne_zero p n (hn.trans hz)

theorem padicFieldToBcris_injective : Function.Injective (PeriodRing.padicFieldToBcris p) :=
  (PeriodRing.padicFieldToBcris p).injective

instance bcris_charZero : CharZero (PeriodRing.Bcris p) where
  cast_injective a b h := by
    have he : (a : ℚ_[p]) = (b : ℚ_[p]) :=
      padicFieldToBcris_injective p (by simpa only [map_natCast] using h)
    exact Nat.cast_injective he

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.NontrivialityT
