import OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamEnvelope

/-! # Cyclotomic -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.WeakAdmissibility.Cyclotomic.LogContinuity

/-!
Integral congruences for the constructed crystalline logarithm.
These estimates use actual divided powers in the crystalline envelope.
-/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm

variable (p : ℕ) [Fact p.Prime]

theorem binomial_factorial (n i : ℕ) :
    (i + 1).factorial * (n + 1).choose (i + 1) =
      (n + 1) * (i.factorial * n.choose i) := by
  calc
    (i + 1).factorial * (n + 1).choose (i + 1) =
        ((n + 1).choose (i + 1) * (i + 1)) * i.factorial := by
      rw [Nat.factorial_succ]
      ring
    _ = ((n + 1) * n.choose i) * i.factorial := by
      rw [← Nat.add_one_mul_choose_eq]
    _ = (n + 1) * (i.factorial * n.choose i) := by ring

/-- Divided powers exhibit an integral factor n in (1+x)^n-1. -/
theorem powerDifference_eq (x : Logarithm.PeriodRings.AInf p) (hx : Logarithm.PeriodRings.thetaModP p x = 0) (n : ℕ) :
    algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p) ((1 + x) ^ (n + 1) - 1) =
      (n + 1 : Logarithm.PeriodRings.ACrisUncompleted p) *
        ∑ i ∈ Finset.range (n + 1),
          (i.factorial * n.choose i : ℕ) * Logarithm.PeriodRings.dividedPower p x (i + 1) hx := by
  rw [map_sub, map_pow, map_add, map_one, add_comm, add_pow, Finset.sum_range_succ']
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one,
    add_sub_cancel_right]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← DeRhamEnvelope.factorial_mul_dividedPower p x hx (i + 1)]
  calc
    ((i + 1).factorial : Logarithm.PeriodRings.ACrisUncompleted p) * Logarithm.PeriodRings.dividedPower p x (i + 1) hx *
        ((n + 1).choose (i + 1) : Logarithm.PeriodRings.ACrisUncompleted p) =
      (((i + 1).factorial * (n + 1).choose (i + 1) : ℕ) : Logarithm.PeriodRings.ACrisUncompleted p) *
        Logarithm.PeriodRings.dividedPower p x (i + 1) hx := by
      rw [Nat.cast_mul]
      ring
    _ = _ := by
      rw [binomial_factorial, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring

theorem powerDifference_dvd (x : Logarithm.PeriodRings.AInf p) (hx : Logarithm.PeriodRings.thetaModP p x = 0) (n : ℕ) :
    (n : Logarithm.PeriodRings.ACrisUncompleted p) ∣
      algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p) ((1 + x) ^ n - 1) := by
  cases n with
  | zero => simp
  | succ n =>
    refine ⟨∑ i ∈ Finset.range (n + 1),
      (i.factorial * n.choose i : ℕ) * Logarithm.PeriodRings.dividedPower p x (i + 1) hx, ?_⟩
    simpa only [Nat.cast_add, Nat.cast_one] using powerDifference_eq p x hx n

theorem powerDifference_mem_p_power (x : Logarithm.PeriodRings.AInf p) (hx : Logarithm.PeriodRings.thetaModP p x = 0) (k : ℕ) :
    algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p) ((1 + x) ^ (p ^ k) - 1) ∈
      (Ideal.span {(p : Logarithm.PeriodRings.ACrisUncompleted p)}) ^ k := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  simpa only [Nat.cast_pow] using powerDifference_dvd p x hx (p ^ k)

/-- An integral coefficient representing p^N/(m+1), with m+1 ≤ N. -/
def logDenominatorCoefficient (m N : ℕ) : Logarithm.PeriodRings.AInf p :=
  PeriodInvariants.AdicEstimates.Frobenius.pDividedPowerCoefficient p (m + 1) * m.factorial * p ^ (N - (m + 1))

theorem logDenominatorCoefficient_fraction (m N : ℕ) (hm : m + 1 ≤ N) :
    algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p) (logDenominatorCoefficient p m N) =
      (p : Logarithm.PeriodRings.AInfFractionField p) ^ N / (m + 1 : Logarithm.PeriodRings.AInfFractionField p) := by
  rw [logDenominatorCoefficient, map_mul, map_mul, map_pow, map_natCast, map_natCast,
    PeriodInvariants.AdicEstimates.Frobenius.pDividedPowerCoefficient_fraction, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  have hf : (m.factorial : Logarithm.PeriodRings.AInfFractionField p) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero m
  have hm' : (m + 1 : Logarithm.PeriodRings.AInfFractionField p) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero m
  have hp : (p : Logarithm.PeriodRings.AInfFractionField p) ^ (m + 1) *
      (p : Logarithm.PeriodRings.AInfFractionField p) ^ (N - (m + 1)) = (p : Logarithm.PeriodRings.AInfFractionField p) ^ N := by
    rw [← pow_add, Nat.add_sub_of_le hm]
  field_simp
  exact hp

/-- A finite logarithm term loses at most N powers of p when its degree is at most N. -/
theorem crystallineLogTerm_congr_mem (x y : Logarithm.PeriodRings.AInf p)
    (hx : Logarithm.PeriodRings.thetaModP p x = 0) (hy : Logarithm.PeriodRings.thetaModP p y = 0) (k N m : ℕ) (hm : m + 1 ≤ N)
    (hxy : algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p) (x - y) ∈
      (Ideal.span {(p : Logarithm.PeriodRings.ACrisUncompleted p)}) ^ (k + N)) :
    Logarithm.PeriodRings.crystallineLogTerm p x hx m - Logarithm.PeriodRings.crystallineLogTerm p y hy m ∈
      (Ideal.span {(p : Logarithm.PeriodRings.ACrisUncompleted p)}) ^ k := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hxy ⊢
  obtain ⟨c, hc⟩ := hxy
  rw [map_sub] at hc
  obtain ⟨q, hq⟩ := (Commute.all
    (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p) x)
    (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p) y)).sub_dvd_pow_sub_pow (m + 1)
  rw [hc] at hq
  have hqf :
      algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p) x ^ (m + 1) -
        algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p) y ^ (m + 1) =
      (p : Logarithm.PeriodRings.AInfFractionField p) ^ (k + N) * (c : Logarithm.PeriodRings.AInfFractionField p) *
        (q : Logarithm.PeriodRings.AInfFractionField p) := by
    simpa only [map_sub, map_pow, map_mul, map_natCast, AlgHom.commutes, Subalgebra.val_apply] using
      congrArg (Logarithm.PeriodRings.aCrisUncompleted p).val hq
  refine ⟨(-1) ^ m * c * q *
    algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p) (logDenominatorCoefficient p m N), ?_⟩
  apply Subtype.ext
  change (Logarithm.PeriodRings.crystallineLogTerm p x hx m : Logarithm.PeriodRings.AInfFractionField p) -
      (Logarithm.PeriodRings.crystallineLogTerm p y hy m : Logarithm.PeriodRings.AInfFractionField p) =
    (p : Logarithm.PeriodRings.AInfFractionField p) ^ k *
      ((-1 : Logarithm.PeriodRings.AInfFractionField p) ^ m * (c : Logarithm.PeriodRings.AInfFractionField p) *
        (q : Logarithm.PeriodRings.AInfFractionField p) *
          algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.AInfFractionField p) (logDenominatorCoefficient p m N))
  rw [Logarithm.PeriodRings.crystallineLogTerm_coe, Logarithm.PeriodRings.crystallineLogTerm_coe,
    logDenominatorCoefficient_fraction p m N hm, ← sub_div, ← mul_sub, hqf, pow_add]
  ring

/-- Explicit continuity estimate for the actual crystalline logarithm modulo p^k. -/
theorem crystallineLog_congr_mod (x y : Logarithm.PeriodRings.AInf p)
    (hx : Logarithm.PeriodRings.thetaModP p x = 0) (hy : Logarithm.PeriodRings.thetaModP p y = 0) (k : ℕ)
    (hxy : algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p) (x - y) ∈
      (Ideal.span {(p : Logarithm.PeriodRings.ACrisUncompleted p)}) ^ (k + p * k)) :
    AdicCompletion.evalₐ (Ideal.span {(p : Logarithm.PeriodRings.ACrisUncompleted p)}) k
        (Logarithm.PeriodRings.crystallineLog p x hx) =
      AdicCompletion.evalₐ (Ideal.span {(p : Logarithm.PeriodRings.ACrisUncompleted p)}) k
        (Logarithm.PeriodRings.crystallineLog p y hy) := by
  rw [Logarithm.PeriodRings.crystallineLog_mod, Logarithm.PeriodRings.crystallineLog_mod, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Ideal.Quotient.eq.mpr
  exact crystallineLogTerm_congr_mem p x y hx hy k (p * k) m
    (Nat.succ_le_iff.mpr (Finset.mem_range.mp hm)) hxy

/-- A sufficiently deep p-power in the ratio gives identical logarithms modulo p^k. -/
theorem crystallineLog_congr_of_power_ratio (x y z : Logarithm.PeriodRings.AInf p)
    (hx : Logarithm.PeriodRings.thetaModP p x = 0) (hy : Logarithm.PeriodRings.thetaModP p y = 0) (hz : Logarithm.PeriodRings.thetaModP p z = 0)
    (k r : ℕ) (hr : k + p * k ≤ r)
    (he : 1 + x = (1 + y) * (1 + z) ^ (p ^ r)) :
    AdicCompletion.evalₐ (Ideal.span {(p : Logarithm.PeriodRings.ACrisUncompleted p)}) k
        (Logarithm.PeriodRings.crystallineLog p x hx) =
      AdicCompletion.evalₐ (Ideal.span {(p : Logarithm.PeriodRings.ACrisUncompleted p)}) k
        (Logarithm.PeriodRings.crystallineLog p y hy) := by
  apply crystallineLog_congr_mod p x y hx hy k
  have hfactor : x - y = (1 + y) * ((1 + z) ^ (p ^ r) - 1) := by
    calc
      x - y = (1 + x) - (1 + y) := by ring
      _ = (1 + y) * ((1 + z) ^ (p ^ r) - 1) := by rw [he]; ring
  rw [hfactor, map_mul]
  apply Ideal.mul_mem_left
  exact Ideal.pow_le_pow_right hr (powerDifference_mem_p_power p z hz r)

end NumberTheory.PadicHodge.WeakAdmissibility.Cyclotomic.LogContinuity

namespace NumberTheory.PadicHodge.WeakAdmissibility.Cyclotomic

/-!
Compatible-root calculations for the cyclotomic period in WeakAdmissibility.
-/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings

variable (p : ℕ) [Fact p.Prime]

section UnitTowers

variable {M : Type*} [CommMonoid M]

theorem towerCoeff_isUnit (a : Perfection M p)
    (ha : Perfection.coeffMonoidHom M p 0 a = 1) (n : ℕ) :
    IsUnit (Perfection.coeffMonoidHom M p n a) :=
  IsUnit.of_pow_eq_one ((Perfection.coeffMonoidHom_pow_p_pow_self a n).trans ha)
    (pow_ne_zero n (Fact.out : p.Prime).ne_zero)

/-- A compatible root tower above one is a tower of units. -/
def unitTower (a : Perfection M p) (ha : Perfection.coeffMonoidHom M p 0 a = 1) :
    Perfection Mˣ p :=
  ⟨fun n => (towerCoeff_isUnit p a ha n).unit, fun n => by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, IsUnit.unit_spec] using
      Perfection.coeffMonoidHom_pow_p' a n⟩

theorem unitTower_coeff (a : Perfection M p)
    (ha : Perfection.coeffMonoidHom M p 0 a = 1) (n : ℕ) :
    ((Perfection.coeffMonoidHom Mˣ p n (unitTower p a ha)) : M) =
      Perfection.coeffMonoidHom M p n a :=
  (towerCoeff_isUnit p a ha n).unit_spec

theorem unitTower_coe (a : Perfection M p)
    (ha : Perfection.coeffMonoidHom M p 0 a = 1) :
    Perfection.mapMonoidHom p (Units.coeHom M) (unitTower p a ha) = a := by
  apply Perfection.extMonoid
  intro n
  exact unitTower_coeff p a ha n

end UnitTowers

section GroupTowers

variable {G : Type*} [CommGroup G]

omit [Fact p.Prime] in
/-- Agreement in coordinate r gives a ratio which is a p^r-th power above one. -/
theorem exists_power_ratio_group (a b : Perfection G p) (r : ℕ)
    (hr : Perfection.coeffMonoidHom G p r a = Perfection.coeffMonoidHom G p r b) :
    ∃ c : Perfection G p, Perfection.coeffMonoidHom G p 0 c = 1 ∧
      a = b * c ^ (p ^ r) := by
  let c : Perfection G p := ⟨fun n =>
    Perfection.coeffMonoidHom G p (n + r) a *
      (Perfection.coeffMonoidHom G p (n + r) b)⁻¹, fun n => by
    rw [mul_pow, inv_pow]
    have hn : n + 1 + r = n + r + 1 := by omega
    rw [hn, Perfection.coeffMonoidHom_pow_p', Perfection.coeffMonoidHom_pow_p']⟩
  refine ⟨c, ?_, ?_⟩
  · change Perfection.coeffMonoidHom G p (0 + r) a *
      (Perfection.coeffMonoidHom G p (0 + r) b)⁻¹ = 1
    rw [Nat.zero_add, hr, mul_inv_cancel]
  · apply Perfection.extMonoid
    intro n
    change Perfection.coeffMonoidHom G p n a =
      Perfection.coeffMonoidHom G p n b *
        (Perfection.coeffMonoidHom G p (n + r) a *
          (Perfection.coeffMonoidHom G p (n + r) b)⁻¹) ^ (p ^ r)
    rw [mul_pow, inv_pow, Perfection.coeffMonoidHom_pow_p_pow',
      Perfection.coeffMonoidHom_pow_p_pow']
    simp

end GroupTowers

section MonoidTowers

variable {M : Type*} [CommMonoid M]

/-- The ratio calculation also applies in a monoid to compatible roots of one. -/
theorem exists_power_ratio (a b : Perfection M p)
    (ha : Perfection.coeffMonoidHom M p 0 a = 1)
    (hb : Perfection.coeffMonoidHom M p 0 b = 1) (r : ℕ)
    (hr : Perfection.coeffMonoidHom M p r a = Perfection.coeffMonoidHom M p r b) :
    ∃ c : Perfection M p, Perfection.coeffMonoidHom M p 0 c = 1 ∧
      a = b * c ^ (p ^ r) := by
  have hru : Perfection.coeffMonoidHom Mˣ p r (unitTower p a ha) =
      Perfection.coeffMonoidHom Mˣ p r (unitTower p b hb) := by
    apply Units.ext
    rw [unitTower_coeff, unitTower_coeff, hr]
  obtain ⟨c, hc, hab⟩ := exists_power_ratio_group p (unitTower p a ha) (unitTower p b hb) r hru
  refine ⟨Perfection.mapMonoidHom p (Units.coeHom M) c, ?_, ?_⟩
  · change ((Perfection.coeffMonoidHom Mˣ p 0 c) : M) = 1
    rw [hc, Units.val_one]
  · have he := congrArg (Perfection.mapMonoidHom p (Units.coeHom M)) hab
    simpa only [map_mul, map_pow, unitTower_coe] using he

end MonoidTowers

/-- The multiplicative Teichmuller map from actual compatible integral roots. -/
def towerToAInf : Perfection 𝓞_ℂ_[p] p →* Logarithm.PeriodRings.AInf p :=
  (WittVector.teichmuller p).comp (PeriodInvariants.PeriodRing.tiltMonoidEquiv p).toMonoidHom

theorem theta_towerToAInf (a : Perfection 𝓞_ℂ_[p] p) :
    Logarithm.PeriodRings.theta p (towerToAInf p a) = Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 a := by
  rw [towerToAInf, MonoidHom.comp_apply, Logarithm.PeriodRings.theta, WittVector.fontaineTheta_teichmuller]
  exact PeriodInvariants.PeriodRing.untilt_tiltMonoidEquiv p a

theorem aInfMap_towerToAInf (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) (a : Perfection 𝓞_ℂ_[p] p) :
    PeriodInvariants.PeriodRing.ainfMap p f (towerToAInf p a) =
      towerToAInf p (Perfection.mapMonoidHom p f.toMonoidHom a) := by
  simp only [towerToAInf, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    PeriodInvariants.PeriodRing.ainfMap_teichmuller]
  exact congrArg (WittVector.teichmuller p) (PeriodInvariants.PeriodRing.tiltMap_rootSequence p f a)

def towerDifference (a : Perfection 𝓞_ℂ_[p] p) : Logarithm.PeriodRings.AInf p := towerToAInf p a - 1

theorem aInfMap_towerDifference (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) (a : Perfection 𝓞_ℂ_[p] p) :
    PeriodInvariants.PeriodRing.ainfMap p f (towerDifference p a) =
      towerDifference p (Perfection.mapMonoidHom p f.toMonoidHom a) := by
  rw [towerDifference, map_sub, map_one, aInfMap_towerToAInf]
  rfl

theorem one_add_towerDifference (a : Perfection 𝓞_ℂ_[p] p) :
    1 + towerDifference p a = towerToAInf p a := by
  unfold towerDifference
  ring

theorem towerDifference_theta (a : Perfection 𝓞_ℂ_[p] p)
    (ha : Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 a = 1) :
    Logarithm.PeriodRings.theta p (towerDifference p a) = 0 := by
  rw [towerDifference, map_sub, map_one, theta_towerToAInf, ha, sub_self]

theorem towerDifference_thetaModP (a : Perfection 𝓞_ℂ_[p] p)
    (ha : Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 a = 1) :
    Logarithm.PeriodRings.thetaModP p (towerDifference p a) = 0 := by
  simp only [Logarithm.PeriodRings.thetaModP, RingHom.comp_apply, towerDifference_theta p a ha, map_zero]

/-- The crystalline logarithm is continuous in compatible-root coordinates. -/
theorem towerLog_congr_mod (a b : Perfection 𝓞_ℂ_[p] p)
    (ha : Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 a = 1)
    (hb : Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 b = 1) (k r : ℕ)
    (hr : k + p * k ≤ r)
    (hab : Perfection.coeffMonoidHom 𝓞_ℂ_[p] p r a =
      Perfection.coeffMonoidHom 𝓞_ℂ_[p] p r b) :
    AdicCompletion.evalₐ (Ideal.span {(p : Logarithm.PeriodRings.ACrisUncompleted p)}) k
        (Logarithm.PeriodRings.crystallineLog p (towerDifference p a) (towerDifference_thetaModP p a ha)) =
      AdicCompletion.evalₐ (Ideal.span {(p : Logarithm.PeriodRings.ACrisUncompleted p)}) k
        (Logarithm.PeriodRings.crystallineLog p (towerDifference p b) (towerDifference_thetaModP p b hb)) := by
  obtain ⟨c, hc, he⟩ := exists_power_ratio p a b ha hb r hab
  apply LogContinuity.crystallineLog_congr_of_power_ratio p
    (towerDifference p a) (towerDifference p b) (towerDifference p c)
    (towerDifference_thetaModP p a ha) (towerDifference_thetaModP p b hb)
    (towerDifference_thetaModP p c hc) k r hr
  rw [one_add_towerDifference, one_add_towerDifference, one_add_towerDifference]
  simpa only [map_mul, map_pow] using congrArg (towerToAInf p) he

theorem towerDifference_cyclotomic :
    towerDifference p (Logarithm.PeriodRings.cyclotomicTower p) = Logarithm.PeriodRings.cyclotomicDifference p := rfl

theorem towerDifference_pow (a : Perfection 𝓞_ℂ_[p] p) (n : ℕ) :
    towerDifference p (a ^ n) = (1 + towerDifference p a) ^ n - 1 := by
  rw [towerDifference, map_pow, one_add_towerDifference]

theorem towerLog_pow (a : Perfection 𝓞_ℂ_[p] p)
    (ha : Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 a = 1) (n : ℕ) :
    Logarithm.PeriodRings.crystallineLog p (towerDifference p (a ^ n))
        (towerDifference_thetaModP p (a ^ n) (by rw [map_pow, ha, one_pow])) =
      (n : Logarithm.PeriodRings.ACris p) * Logarithm.PeriodRings.crystallineLog p (towerDifference p a) (towerDifference_thetaModP p a ha) := by
  convert Logarithm.crystallineLog_power p (towerDifference p a)
    (towerDifference_thetaModP p a ha) n using 1
  congr 1
  exact towerDifference_pow p a n

theorem cyclotomicTower_zero :
    Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 (Logarithm.PeriodRings.cyclotomicTower p) = 1 := rfl

def galoisCyclotomicTower (σ : PeriodInvariants.PeriodRing.PadicGalois p) : Perfection 𝓞_ℂ_[p] p :=
  Perfection.mapMonoidHom p (PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ).toMonoidHom (Logarithm.PeriodRings.cyclotomicTower p)

theorem galoisCyclotomicTower_zero (σ : PeriodInvariants.PeriodRing.PadicGalois p) :
    Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 (galoisCyclotomicTower p σ) = 1 :=
  (PeriodInvariants.PeriodRing.galoisIntegerEquiv p σ).map_one

/-- The actual cyclotomic character, reduced to an integer modulo p^r. -/
def cyclotomicExponent (σ : PeriodInvariants.PeriodRing.PadicGalois p) (r : ℕ) : ℕ :=
  ((cyclotomicCharacter ℂ_[p] p (PeriodInvariants.PeriodRing.galoisComplexEquiv p σ)).val.toZModPow r).val

theorem galoisCyclotomicTower_coeff (σ : PeriodInvariants.PeriodRing.PadicGalois p) (r : ℕ) :
    Perfection.coeffMonoidHom 𝓞_ℂ_[p] p r (galoisCyclotomicTower p σ) =
      Perfection.coeffMonoidHom 𝓞_ℂ_[p] p r (Logarithm.PeriodRings.cyclotomicTower p ^ cyclotomicExponent p σ r) := by
  have ht :
      ((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p r (Logarithm.PeriodRings.cyclotomicTower p) : 𝓞_ℂ_[p]) : ℂ_[p]) ^
        (p ^ r) = 1 := by
    have he := (Perfection.coeffMonoidHom_pow_p_pow_self (Logarithm.PeriodRings.cyclotomicTower p) r).trans
      (cyclotomicTower_zero p)
    exact_mod_cast he
  apply Subtype.ext
  change PeriodInvariants.PeriodRing.galoisComplexEquiv p σ
      ((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p r (Logarithm.PeriodRings.cyclotomicTower p) : 𝓞_ℂ_[p]) : ℂ_[p]) =
    (((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p r (Logarithm.PeriodRings.cyclotomicTower p) : 𝓞_ℂ_[p]) : ℂ_[p]) ^
      cyclotomicExponent p σ r)
  exact cyclotomicCharacter.spec (L := ℂ_[p]) p (PeriodInvariants.PeriodRing.galoisComplexEquiv p σ) _ ht

/-- The transformed cyclotomic logarithm has the expected character modulo each p-power. -/
theorem galoisCyclotomicLog_mod (σ : PeriodInvariants.PeriodRing.PadicGalois p) (k : ℕ) :
    AdicCompletion.evalₐ (Ideal.span {(p : Logarithm.PeriodRings.ACrisUncompleted p)}) k
      (Logarithm.PeriodRings.crystallineLog p (towerDifference p (galoisCyclotomicTower p σ))
        (towerDifference_thetaModP p _ (galoisCyclotomicTower_zero p σ))) =
      AdicCompletion.evalₐ (Ideal.span {(p : Logarithm.PeriodRings.ACrisUncompleted p)}) k
        ((cyclotomicExponent p σ (k + p * k) : Logarithm.PeriodRings.ACris p) * Logarithm.PeriodRings.cyclotomicPeriod p) := by
  have h := towerLog_congr_mod p (galoisCyclotomicTower p σ)
    (Logarithm.PeriodRings.cyclotomicTower p ^ cyclotomicExponent p σ (k + p * k))
    (galoisCyclotomicTower_zero p σ)
    (by rw [map_pow, cyclotomicTower_zero, one_pow]) k (k + p * k) le_rfl
    (galoisCyclotomicTower_coeff p σ (k + p * k))
  rw [towerLog_pow p (Logarithm.PeriodRings.cyclotomicTower p) (cyclotomicTower_zero p)] at h
  exact h

def padicIntToEnvelope : ℤ_[p] →+* Logarithm.PeriodRings.ACrisUncompleted p :=
  (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.ACrisUncompleted p)).comp (Logarithm.PeriodRings.padicIntToAInf p)

def padicIntToACris : ℤ_[p] →+* Logarithm.PeriodRings.ACris p :=
  (algebraMap (Logarithm.PeriodRings.ACrisUncompleted p) (Logarithm.PeriodRings.ACris p)).comp (padicIntToEnvelope p)

theorem padicIntToACris_eval (a : ℤ_[p]) (k : ℕ) :
    AdicCompletion.evalₐ (Ideal.span {(p : Logarithm.PeriodRings.ACrisUncompleted p)}) k (padicIntToACris p a) =
      Ideal.Quotient.mk _ (padicIntToEnvelope p a) := by
  change AdicCompletion.evalₐ (Ideal.span {(p : Logarithm.PeriodRings.ACrisUncompleted p)}) k
    (AdicCompletion.of (Ideal.span {(p : Logarithm.PeriodRings.ACrisUncompleted p)}) (Logarithm.PeriodRings.ACrisUncompleted p)
      (padicIntToEnvelope p a)) = _
  rw [AdicCompletion.evalₐ_of]

/-- Integer residues compute the canonical p-adic coefficient map modulo p^k. -/
theorem padicIntToACris_mod (a : ℤ_[p]) (k r : ℕ) (hkr : k ≤ r) :
    AdicCompletion.evalₐ (Ideal.span {(p : Logarithm.PeriodRings.ACrisUncompleted p)}) k (padicIntToACris p a) =
      ((a.toZModPow r).val : (Logarithm.PeriodRings.ACrisUncompleted p) ⧸
        (Ideal.span {(p : Logarithm.PeriodRings.ACrisUncompleted p)}) ^ k) := by
  have hdiff : a - ((a.toZModPow r).val : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ r} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]
    simp only [map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hdiff
  have he : padicIntToEnvelope p a - ((a.toZModPow r).val : Logarithm.PeriodRings.ACrisUncompleted p) =
      (p : Logarithm.PeriodRings.ACrisUncompleted p) ^ r * padicIntToEnvelope p c := by
    simpa only [map_sub, map_mul, map_pow, map_natCast] using congrArg (padicIntToEnvelope p) hc
  have hmem : padicIntToEnvelope p a - ((a.toZModPow r).val : Logarithm.PeriodRings.ACrisUncompleted p) ∈
      (Ideal.span {(p : Logarithm.PeriodRings.ACrisUncompleted p)}) ^ r := by
    rw [he]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) r)
  rw [padicIntToACris_eval]
  change Ideal.Quotient.mk _ (padicIntToEnvelope p a) =
    Ideal.Quotient.mk _ ((a.toZModPow r).val : Logarithm.PeriodRings.ACrisUncompleted p)
  exact Ideal.Quotient.eq.mpr (Ideal.pow_le_pow_right hkr hmem)

/-- The transformed cyclotomic logarithm scales by the actual p-adic cyclotomic character. -/
theorem galoisCyclotomicLog_character (σ : PeriodInvariants.PeriodRing.PadicGalois p) :
    Logarithm.PeriodRings.crystallineLog p (towerDifference p (galoisCyclotomicTower p σ))
        (towerDifference_thetaModP p _ (galoisCyclotomicTower_zero p σ)) =
      padicIntToACris p (cyclotomicCharacter ℂ_[p] p (PeriodInvariants.PeriodRing.galoisComplexEquiv p σ)).val *
        Logarithm.PeriodRings.cyclotomicPeriod p := by
  apply AdicCompletion.ext_evalₐ
  intro k
  rw [galoisCyclotomicLog_mod, map_mul, map_natCast, map_mul,
    padicIntToACris_mod p _ k (k + p * k) (Nat.le_add_right _ _)]
  rfl

end NumberTheory.PadicHodge.WeakAdmissibility.Cyclotomic

end

end OAI
