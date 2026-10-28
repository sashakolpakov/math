import OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteComparison
import OAI.NumberTheory.PadicHodge.PeriodInvariants.DeRhamStructure

/-! # De Rham Logarithm -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.PeriodInvariants.DeRhamLogarithm.Comparison

/-!
# The actual crystalline-to-de-Rham period map

The compatible maps to finite theta quotients assemble into a ring map to
Mathlib's native BDeRhamPlus. Inverting p extends it to B_cris-plus.
-/

section Quotients

variable {R : Type*} [CommRing R] {I J I' J' : Ideal R}

theorem quotientEquiv_factor (eI : I = I') (eJ : J = J') (h : I ≤ J) (h' : I' ≤ J')
    (x : R ⧸ I) :
    Ideal.Quotient.factor h' (Ideal.quotEquivOfEq eI x) =
      Ideal.quotEquivOfEq eJ (Ideal.Quotient.factor h x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.quotEquivOfEq_mk]
  rfl

end Quotients

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing OAI.NumberTheory.PadicHodge.PeriodInvariants.ThetaKernel OAI.NumberTheory.PadicHodge.PeriodInvariants.Nontriviality OAI.NumberTheory.PadicHodge.PeriodInvariants.DeRhamStructure
  FiniteLattices.Period FiniteComparison FiniteComparison.Compatibility

variable (p : ℕ) [Fact p.Prime]

theorem rationalIdeal_eq_native (N : ℕ) :
    (Ideal.span {ThetaKernel.xi p ^ N}).map (algebraMap (PeriodRing.Ainf p) (Nontriviality.Binf p)) =
      (RingHom.ker (DeRhamStructure.nativeTheta p)) ^ N := by
  rw [DeRhamStructure.nativeTheta_kernel, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, map_pow]

def nativeFiniteComparison (N : ℕ) :
    PeriodRing.Acris p →+* Nontriviality.Binf p ⧸ (RingHom.ker (DeRhamStructure.nativeTheta p)) ^ N :=
  (Ideal.quotEquivOfEq (rationalIdeal_eq_native p N)).toRingHom.comp (FiniteComparison.acrisToFiniteQuotient p N)

theorem nativeFiniteComparison_compatible {M N : ℕ} (h : M ≤ N) (x : PeriodRing.Acris p) :
    Ideal.Quotient.factorPow (RingHom.ker (DeRhamStructure.nativeTheta p)) h (nativeFiniteComparison p N x) =
      nativeFiniteComparison p M x := by
  change Ideal.Quotient.factor (Ideal.pow_le_pow_right h)
      (Ideal.quotEquivOfEq (rationalIdeal_eq_native p N) (FiniteComparison.acrisToFiniteQuotient p N x)) = _
  rw [quotientEquiv_factor (rationalIdeal_eq_native p N) (rationalIdeal_eq_native p M)
    (Ideal.map_mono (FiniteComparison.Compatibility.thetaPower_le p h))]
  exact congrArg (Ideal.quotEquivOfEq (rationalIdeal_eq_native p M))
    (FiniteComparison.Compatibility.acrisToFiniteQuotient_compatible p h x)

/-- A ring map from the actual completed crystalline envelope to native B_dR-plus. -/
def acrisToDeRhamPlus : PeriodRing.Acris p →+* BDeRhamPlus 𝓞_ℂ_[p] p :=
  AdicCompletion.liftRingHom (RingHom.ker (DeRhamStructure.nativeTheta p)) (nativeFiniteComparison p)
    (by
      intro M N h
      ext x
      exact nativeFiniteComparison_compatible p h x)

theorem acrisToDeRhamPlus_eval (N : ℕ) (x : PeriodRing.Acris p) :
    AdicCompletion.evalₐ (RingHom.ker (DeRhamStructure.nativeTheta p)) N (acrisToDeRhamPlus p x) =
      nativeFiniteComparison p N x := by
  exact AdicCompletion.evalₐ_liftRingHom (RingHom.ker (DeRhamStructure.nativeTheta p))
    (nativeFiniteComparison p) (by
      intro M N h
      ext a
      exact nativeFiniteComparison_compatible p h a) N x

theorem acrisToDeRhamPlus_of (x : PeriodRing.AcrisZero p) :
    acrisToDeRhamPlus p (AdicCompletion.of (Ideal.span {(p : PeriodRing.AcrisZero p)}) _ x) =
      DeRhamStructure.binfToDeRhamPlus p (Nontriviality.acrisZeroToBinf p x) := by
  apply AdicCompletion.ext_evalₐ
  intro N
  have hm : Ideal.quotEquivOfEq (rationalIdeal_eq_native p N)
      (FiniteComparison.acrisToFiniteQuotient p N (AdicCompletion.of (Ideal.span {(p : PeriodRing.AcrisZero p)}) _ x)) =
      Ideal.Quotient.mk ((RingHom.ker (DeRhamStructure.nativeTheta p)) ^ N) (Nontriviality.acrisZeroToBinf p x) := by
    rw [FiniteComparison.acrisToFiniteQuotient_of]
    exact Ideal.quotEquivOfEq_mk (rationalIdeal_eq_native p N) (Nontriviality.acrisZeroToBinf p x)
  exact (acrisToDeRhamPlus_eval p N _).trans (hm.trans
    (AdicCompletion.evalₐ_of (RingHom.ker (DeRhamStructure.nativeTheta p)) N (Nontriviality.acrisZeroToBinf p x)).symm)

theorem p_isUnit_deRhamPlus : IsUnit (p : BDeRhamPlus 𝓞_ℂ_[p] p) := by
  have h := (Nontriviality.p_isUnit_binf p).map (DeRhamStructure.binfToDeRhamPlus p)
  simpa only [map_natCast] using h

/-- Extend the actual period map after p is inverted. -/
def bcrisPlusToDeRhamPlus : PeriodRing.BcrisPlus p →+* BDeRhamPlus 𝓞_ℂ_[p] p :=
  IsLocalization.Away.lift (p : PeriodRing.Acris p) (g := acrisToDeRhamPlus p)
    (by rw [map_natCast]; exact p_isUnit_deRhamPlus p)

theorem bcrisPlusToDeRhamPlus_algebraMap (x : PeriodRing.Acris p) :
    bcrisPlusToDeRhamPlus p (algebraMap (PeriodRing.Acris p) (PeriodRing.BcrisPlus p) x) = acrisToDeRhamPlus p x :=
  IsLocalization.Away.lift_eq _ _ x

end NumberTheory.PadicHodge.PeriodInvariants.DeRhamLogarithm.Comparison

namespace NumberTheory.PadicHodge.PeriodInvariants.DeRhamLogarithm.Finite

/-!
# The crystalline logarithm in finite de Rham quotients

In each finite theta quotient the logarithm becomes a finite sum. The proof
uses the integral lattice and its p-adic completeness to pass from the actual
p-adic logarithm to that sum.
-/

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing OAI.NumberTheory.PadicHodge.PeriodInvariants.PrincipalEnvelope OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteLattices.Period
  FiniteComparison AdditiveCompletion

variable (p : ℕ) [Fact p.Prime]

def truncatedLog (x : RingHom.ker (PeriodRing.theta p)) (N : ℕ) : PeriodRing.AcrisZero p :=
  ∑ k ∈ Finset.range N, PeriodRing.logTerm p x k

theorem projection_dividedPower_zero (x : RingHom.ker (PeriodRing.theta p)) (N n : ℕ) (hn : N ≤ n) :
    FiniteLattices.Period.envelopeProjection p N (PeriodRing.dividedPower p n x) = 0 := by
  obtain ⟨a, ha⟩ := PrincipalEnvelope.dividedPower_eq_smul_xi p n x
  rw [ha]
  simp only [map_smul, FiniteLattices.Period.projection_dividedPower_vanishes p N n hn, smul_zero]

theorem projection_logTerm_zero (x : RingHom.ker (PeriodRing.theta p)) (N k : ℕ) (hk : N ≤ k) :
    FiniteLattices.Period.envelopeProjection p N (PeriodRing.logTerm p x k) = 0 := by
  simp only [PeriodRing.logTerm, map_mul, projection_dividedPower_zero p x N (k + 1) (by omega), mul_zero]

theorem projection_logPartialSum (x : RingHom.ker (PeriodRing.theta p)) (N r : ℕ) (hr : N ≤ r) :
    FiniteLattices.Period.envelopeProjection p N (PeriodRing.logPartialSum p x r) = FiniteLattices.Period.envelopeProjection p N (truncatedLog p x N) := by
  simp only [PeriodRing.logPartialSum, truncatedLog, map_sum]
  have hlen : N ≤ p * r := by nlinarith [(Fact.out : p.Prime).one_lt]
  apply (Finset.sum_subset (Finset.range_mono hlen) ?_).symm
  intro k hk hkN
  exact projection_logTerm_zero p x N k (by simpa only [Finset.mem_range, not_lt] using hkN)

theorem integralLift_logPartialSum (x : RingHom.ker (PeriodRing.theta p)) (N r : ℕ) (hr : N ≤ r) :
    FiniteComparison.integralLiftAddMap p N (PeriodRing.logPartialSum p x r) = FiniteComparison.integralLiftAddMap p N (truncatedLog p x N) := by
  apply FiniteLattices.Period.integralQuotient_injective p N
  change algebraMap (FiniteLattices.Period.IntegralQuotient p N) (FiniteLattices.Period.RationalQuotient p N)
      (FiniteComparison.integralLift p N (PeriodRing.logPartialSum p x r)) =
    algebraMap (FiniteLattices.Period.IntegralQuotient p N) (FiniteLattices.Period.RationalQuotient p N)
      (FiniteComparison.integralLift p N (truncatedLog p x N))
  rw [FiniteComparison.integralLift_spec, FiniteComparison.integralLift_spec, projection_logPartialSum p x N r hr]

theorem extendedIntegralLift_pdLog (x : RingHom.ker (PeriodRing.theta p)) (N : ℕ) :
    AdditiveCompletion.extendAddMap p (FiniteComparison.integralLiftAddMap p N) (PeriodRing.pdLog p x) =
      FiniteComparison.integralLiftAddMap p N (truncatedLog p x N) := by
  apply AdicCompletion.of_injective (Ideal.span {(p : FiniteLattices.Period.IntegralQuotient p N)}) (FiniteLattices.Period.IntegralQuotient p N)
  apply AdicCompletion.ext_evalₐ
  intro r
  rw [AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of]
  have h : Ideal.Quotient.mk ((Ideal.span {(p : FiniteLattices.Period.IntegralQuotient p N)}) ^ (r + N))
      (AdditiveCompletion.extendAddMap p (FiniteComparison.integralLiftAddMap p N) (PeriodRing.pdLog p x)) =
    Ideal.Quotient.mk ((Ideal.span {(p : FiniteLattices.Period.IntegralQuotient p N)}) ^ (r + N))
      (FiniteComparison.integralLiftAddMap p N (truncatedLog p x N)) := by
    rw [AdditiveCompletion.extendAddMap_eval, PeriodRing.pdLog_eval, AdditiveCompletion.quotientAddMap_mk,
      integralLift_logPartialSum p x N (r + N) (by omega)]
  have hh := congrArg
    (Ideal.Quotient.factorPow (Ideal.span {(p : FiniteLattices.Period.IntegralQuotient p N)}) (show r ≤ r + N by omega)) h
  exact hh

/-- The constructed finite crystalline map sends the actual logarithm to its finite truncation. -/
theorem acrisToFiniteQuotient_pdLog (x : RingHom.ker (PeriodRing.theta p)) (N : ℕ) :
    FiniteComparison.acrisToFiniteQuotient p N (PeriodRing.pdLog p x) = FiniteLattices.Period.envelopeProjection p N (truncatedLog p x N) := by
  apply (FiniteLattices.Period.factorial_unit p N N).mul_left_cancel
  rw [FiniteComparison.acrisToFiniteQuotient_scaled]
  change algebraMap (FiniteLattices.Period.IntegralQuotient p N) (FiniteLattices.Period.RationalQuotient p N)
      (AdditiveCompletion.extendAddMap p (FiniteComparison.integralLiftAddMap p N) (PeriodRing.pdLog p x)) = _
  rw [extendedIntegralLift_pdLog]
  exact FiniteComparison.integralLift_spec p N (truncatedLog p x N)

end NumberTheory.PadicHodge.PeriodInvariants.DeRhamLogarithm.Finite

namespace NumberTheory.PadicHodge.PeriodInvariants.DeRhamLogarithm

/-!
# The unit factor in the de Rham logarithm

The usual formal logarithm divided by its argument converges in the theta-adic
completion and is congruent to one modulo theta. It is therefore a unit.
-/

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing OAI.NumberTheory.PadicHodge.PeriodInvariants.Nontriviality OAI.NumberTheory.PadicHodge.PeriodInvariants.DeRhamStructure OAI.NumberTheory.PadicHodge.PeriodInvariants.DeRhamLogarithm.Comparison OAI.NumberTheory.PadicHodge.PeriodInvariants.DeRhamLogarithm.Finite

section Units

variable {R : Type*} [CommRing R] (I : Ideal R) (hI : I.FG)

include hI

theorem completion_isUnit_of_evalOne (x : AdicCompletion I R)
    (hx : AdicCompletion.evalOneₐ I x = 1) : IsUnit x := by
  let _ : IsAdicComplete (I.map (algebraMap R (AdicCompletion I R))) (AdicCompletion I R) :=
    AdicCompletion.isAdicComplete_self I hI
  apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
  apply IsAdicComplete.le_jacobson_bot (I.map (algebraMap R (AdicCompletion I R)))
  have hm : x - 1 ∈ RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom := by
    change AdicCompletion.evalOneₐ I (x - 1) = 0
    rw [map_sub, hx, map_one, sub_self]
  have he : RingHom.ker (AdicCompletion.evalOneₐ I).toRingHom =
      I.map (algebraMap R (AdicCompletion I R)) := AdicCompletion.ker_evalOneₐ_eq_map I hI
  exact he ▸ hm

end Units

section Formula

variable {F : Type*} [Field F] [CharZero F]

theorem logTerm_fraction (z : F) (k : ℕ) :
    (-1 : F) ^ k * (k.factorial : F) * (z ^ (k + 1) / ((k + 1).factorial : F)) =
      ((-1 : F) ^ k / (k + 1 : ℕ)) * z ^ (k + 1) := by
  rw [Nat.factorial_succ, Nat.cast_mul]
  have hk : (k.factorial : F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hk' : (k + 1 : F) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  push_cast
  field_simp

end Formula

variable (p : ℕ) [Fact p.Prime]

def logCoefficient (k : ℕ) : Nontriviality.Binf p := Nontriviality.padicToBinf p ((-1 : ℚ_[p]) ^ k / (k + 1 : ℕ))

theorem logCoefficient_zero : logCoefficient p 0 = 1 := by
  simp only [logCoefficient, pow_zero, zero_add, Nat.cast_one, div_one, map_one]

theorem logCoefficient_fraction (k : ℕ) :
    Nontriviality.binfToFraction p (logCoefficient p k) =
      (-1 : FractionRing (PeriodRing.Ainf p)) ^ k / (k + 1 : ℕ) := by
  change ((Nontriviality.binfToFraction p).comp (Nontriviality.padicToBinf p)) ((-1 : ℚ_[p]) ^ k / (k + 1 : ℕ)) = _
  rw [map_div₀, map_pow, map_neg, map_one, map_natCast]

theorem logTerm_toBinf (x : RingHom.ker (PeriodRing.theta p)) (k : ℕ) :
    Nontriviality.acrisZeroToBinf p (PeriodRing.logTerm p x k) =
      logCoefficient p k * algebraMap (PeriodRing.Ainf p) (Nontriviality.Binf p) (x : PeriodRing.Ainf p) ^ (k + 1) := by
  apply Nontriviality.binfToFraction_injective p
  change Nontriviality.binfToFraction p (Nontriviality.acrisZeroLift p (PeriodRing.logTerm p x k)) = _
  rw [Nontriviality.acrisZeroLift_spec, map_mul, logCoefficient_fraction, map_pow, Nontriviality.binfToFraction_algebraMap]
  change (-1 : FractionRing (PeriodRing.Ainf p)) ^ k * (k.factorial : FractionRing (PeriodRing.Ainf p)) *
      (algebraMap (PeriodRing.Ainf p) (FractionRing (PeriodRing.Ainf p)) (x : PeriodRing.Ainf p) ^ (k + 1) /
        ((k + 1).factorial : FractionRing (PeriodRing.Ainf p))) = _
  exact logTerm_fraction _ k

def logUnitPartialSum (x : RingHom.ker (PeriodRing.theta p)) (N : ℕ) : Nontriviality.Binf p :=
  ∑ k ∈ Finset.range N, logCoefficient p k * algebraMap (PeriodRing.Ainf p) (Nontriviality.Binf p) (x : PeriodRing.Ainf p) ^ k

theorem kernel_algebraMap (x : RingHom.ker (PeriodRing.theta p)) :
    algebraMap (PeriodRing.Ainf p) (Nontriviality.Binf p) (x : PeriodRing.Ainf p) ∈ RingHom.ker (DeRhamStructure.nativeTheta p) := by
  rw [RingHom.mem_ker, DeRhamStructure.nativeTheta_algebraMap, RingHom.mem_ker.mp x.property, map_zero]

theorem logUnitPartialSum_cauchy (x : RingHom.ker (PeriodRing.theta p)) :
    AdicCompletion.IsAdicCauchy (RingHom.ker (DeRhamStructure.nativeTheta p)) (Nontriviality.Binf p) (logUnitPartialSum p x) := by
  rw [AdicCompletion.isAdicCauchy_iff]
  intro n
  apply SModEq.symm
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  change logUnitPartialSum p x (n + 1) - logUnitPartialSum p x n ∈ _
  rw [logUnitPartialSum, logUnitPartialSum, Finset.sum_range_succ, add_sub_cancel_left]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (kernel_algebraMap p x) n)

def deRhamLogUnit (x : RingHom.ker (PeriodRing.theta p)) :
    AdicCompletion (RingHom.ker (DeRhamStructure.nativeTheta p)) (Nontriviality.Binf p) :=
  AdicCompletion.mk (RingHom.ker (DeRhamStructure.nativeTheta p)) (Nontriviality.Binf p)
    ⟨logUnitPartialSum p x, logUnitPartialSum_cauchy p x⟩

theorem deRhamLogUnit_eval (x : RingHom.ker (PeriodRing.theta p)) (N : ℕ) :
    AdicCompletion.evalₐ (RingHom.ker (DeRhamStructure.nativeTheta p)) N (deRhamLogUnit p x) =
      Ideal.Quotient.mk ((RingHom.ker (DeRhamStructure.nativeTheta p)) ^ N) (logUnitPartialSum p x N) :=
  AdicCompletion.evalₐ_mk _ N ⟨logUnitPartialSum p x, logUnitPartialSum_cauchy p x⟩

theorem deRhamLogUnit_evalOne (x : RingHom.ker (PeriodRing.theta p)) :
    AdicCompletion.evalOneₐ (RingHom.ker (DeRhamStructure.nativeTheta p)) (deRhamLogUnit p x) = 1 := by
  rw [← AdicCompletion.factorₐ_evalₐ_one]
  rw [deRhamLogUnit_eval]
  simp only [logUnitPartialSum, Finset.sum_range_one, logCoefficient_zero, pow_zero,
    mul_one, map_one]

theorem deRhamLogUnit_isUnit (x : RingHom.ker (PeriodRing.theta p)) : IsUnit (deRhamLogUnit p x) :=
  completion_isUnit_of_evalOne (RingHom.ker (DeRhamStructure.nativeTheta p))
    (by rw [DeRhamStructure.nativeTheta_kernel]; exact Submodule.fg_span_singleton _) _ (deRhamLogUnit_evalOne p x)

theorem truncatedLog_factor (x : RingHom.ker (PeriodRing.theta p)) (N : ℕ) :
    Nontriviality.acrisZeroToBinf p (Finite.truncatedLog p x N) =
      algebraMap (PeriodRing.Ainf p) (Nontriviality.Binf p) (x : PeriodRing.Ainf p) * logUnitPartialSum p x N := by
  rw [Finite.truncatedLog, map_sum, logUnitPartialSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [logTerm_toBinf, pow_succ']
  ring

end NumberTheory.PadicHodge.PeriodInvariants.DeRhamLogarithm

end

end OAI
