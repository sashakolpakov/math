import OAI.NumberTheory.PadicHodge.WeakAdmissibility.Cyclotomic
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.AdicGeneration

/-! # Theta Kernel -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaKernel

noncomputable section

/-!
The principal kernel of Fontaine theta for the actual completed algebraic
closure. Divisibility in the tilt is proved using compatible integral roots.
-/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.Cyclotomic
open scoped NNReal

variable (p : ℕ) [Fact p.Prime]

theorem towerCoeff_ne_zero (b : Perfection 𝓞_ℂ_[p] p)
    (hb : Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 b ≠ 0) (n : ℕ) :
    Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n b ≠ 0 := by
  intro hn
  have he := Perfection.coeffMonoidHom_pow_p_pow_self b n
  rw [hn, zero_pow (pow_ne_zero n (Fact.out : p.Prime).ne_zero)] at he
  exact hb he.symm

theorem towerCoeff_norm_le (a b : Perfection 𝓞_ℂ_[p] p)
    (hab : ‖((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 a : 𝓞_ℂ_[p]) : ℂ_[p])‖ ≤
      ‖((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 b : 𝓞_ℂ_[p]) : ℂ_[p])‖) (n : ℕ) :
    ‖((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n a : 𝓞_ℂ_[p]) : ℂ_[p])‖ ≤
      ‖((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n b : 𝓞_ℂ_[p]) : ℂ_[p])‖ := by
  apply (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _)
    (pow_ne_zero n (Fact.out : p.Prime).ne_zero)).mp
  have he (c : Perfection 𝓞_ℂ_[p] p) :
      ((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n c : 𝓞_ℂ_[p]) : ℂ_[p]) ^ (p ^ n) =
        ((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 c : 𝓞_ℂ_[p]) : ℂ_[p]) := by
    exact_mod_cast Perfection.coeffMonoidHom_pow_p_pow_self c n
  simpa only [← norm_pow, he a, he b] using hab

def quotientCoefficient (a b : Perfection 𝓞_ℂ_[p] p)
    (hb : Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 b ≠ 0)
    (hab : ‖((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 a : 𝓞_ℂ_[p]) : ℂ_[p])‖ ≤
      ‖((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 b : 𝓞_ℂ_[p]) : ℂ_[p])‖) (n : ℕ) : 𝓞_ℂ_[p] :=
  ⟨((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n a : 𝓞_ℂ_[p]) : ℂ_[p]) /
    ((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n b : 𝓞_ℂ_[p]) : ℂ_[p]), by
    have hb' : ((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n b : 𝓞_ℂ_[p]) : ℂ_[p]) ≠ 0 := by
      exact_mod_cast towerCoeff_ne_zero p b hb n
    have hn : ‖((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n a : 𝓞_ℂ_[p]) : ℂ_[p]) /
        ((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n b : 𝓞_ℂ_[p]) : ℂ_[p])‖ ≤ 1 := by
      rw [norm_div]
      exact (div_le_one (norm_pos_iff.mpr hb')).mpr (towerCoeff_norm_le p a b hab n)
    change (Valued.v _ : ℝ≥0) ≤ 1
    rw [Logarithm.PeriodRings.valuation_eq_nnnorm]
    exact_mod_cast hn⟩

theorem quotientCoefficient_pow (a b : Perfection 𝓞_ℂ_[p] p)
    (hb : Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 b ≠ 0)
    (hab : ‖((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 a : 𝓞_ℂ_[p]) : ℂ_[p])‖ ≤
      ‖((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 b : 𝓞_ℂ_[p]) : ℂ_[p])‖) (n : ℕ) :
    quotientCoefficient p a b hb hab (n + 1) ^ p = quotientCoefficient p a b hb hab n := by
  apply Subtype.ext
  change (((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p (n + 1) a : 𝓞_ℂ_[p]) : ℂ_[p]) /
      ((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p (n + 1) b : 𝓞_ℂ_[p]) : ℂ_[p])) ^ p = _
  have he (c : Perfection 𝓞_ℂ_[p] p) :
      ((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p (n + 1) c : 𝓞_ℂ_[p]) : ℂ_[p]) ^ p =
        ((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n c : 𝓞_ℂ_[p]) : ℂ_[p]) := by
    exact_mod_cast Perfection.coeffMonoidHom_pow_p' c n
  rw [div_pow, he a, he b]
  rfl

/-- Division of compatible roots remains integral when their zeroth norms are ordered. -/
theorem tower_dvd_of_norm_le (a b : Perfection 𝓞_ℂ_[p] p)
    (hb : Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 b ≠ 0)
    (hab : ‖((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 a : 𝓞_ℂ_[p]) : ℂ_[p])‖ ≤
      ‖((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 b : 𝓞_ℂ_[p]) : ℂ_[p])‖) :
    b ∣ a := by
  refine ⟨⟨quotientCoefficient p a b hb hab, quotientCoefficient_pow p a b hb hab⟩, ?_⟩
  apply Perfection.extMonoid
  intro n
  apply Subtype.ext
  change ((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n a : 𝓞_ℂ_[p]) : ℂ_[p]) =
    ((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n b : 𝓞_ℂ_[p]) : ℂ_[p]) *
      (((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n a : 𝓞_ℂ_[p]) : ℂ_[p]) /
        ((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n b : 𝓞_ℂ_[p]) : ℂ_[p]))
  have hb' : ((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n b : 𝓞_ℂ_[p]) : ℂ_[p]) ≠ 0 := by
    exact_mod_cast towerCoeff_ne_zero p b hb n
  simpa only [mul_comm] using (div_mul_cancel₀
    ((Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n a : 𝓞_ℂ_[p]) : ℂ_[p]) hb').symm

/-- Divisibility in the actual tilt follows from the untilted absolute values. -/
theorem tilt_dvd_of_untilt_norm_le (a b : PreTilt 𝓞_ℂ_[p] p) (hb : b.untilt ≠ 0)
    (hab : ‖(a.untilt : ℂ_[p])‖ ≤ ‖(b.untilt : ℂ_[p])‖) : b ∣ a := by
  let e := PeriodInvariants.PeriodRing.tiltMonoidEquiv p
  have hcoord (c : PreTilt 𝓞_ℂ_[p] p) :
      Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 (e.symm c) = c.untilt := by
    have he := PeriodInvariants.PeriodRing.untilt_tiltMonoidEquiv p (e.symm c)
    change (e (e.symm c)).untilt = _ at he
    rw [e.apply_symm_apply] at he
    exact he.symm
  obtain ⟨c, hc⟩ := tower_dvd_of_norm_le p (e.symm a) (e.symm b)
    (by rwa [hcoord]) (by simpa only [hcoord] using hab)
  refine ⟨e c, ?_⟩
  simpa only [map_mul, e.apply_symm_apply] using congrArg e hc

/-- A compatible sequence p, p^(1/p), p^(1/p²),... in the actual integral closure. -/
def pTower : Perfection 𝓞_ℂ_[p] p :=
  ⟨fun n => (Logarithm.PeriodRings.integerRoot p)^[n] (p : 𝓞_ℂ_[p]), fun n => by
    change ((Logarithm.PeriodRings.integerRoot p)^[n + 1] (p : 𝓞_ℂ_[p])) ^ p = (Logarithm.PeriodRings.integerRoot p)^[n] (p : 𝓞_ℂ_[p])
    rw [Function.iterate_succ_apply']
    exact Logarithm.PeriodRings.integerRoot_pow p _⟩

def pFlat : PreTilt 𝓞_ℂ_[p] p := PeriodInvariants.PeriodRing.tiltMonoidEquiv p (pTower p)

theorem pFlat_untilt : (pFlat p).untilt = (p : 𝓞_ℂ_[p]) :=
  PeriodInvariants.PeriodRing.untilt_tiltMonoidEquiv p (pTower p)

theorem pFlat_untilt_ne_zero : (pFlat p).untilt ≠ 0 := by
  rw [pFlat_untilt]
  exact_mod_cast (Fact.out : p.Prime).ne_zero

theorem pFlat_ne_zero : pFlat p ≠ 0 := by
  intro h
  have hz : (0 : PreTilt 𝓞_ℂ_[p] p).untilt = 0 := Perfection.teichmuller_zero
  exact pFlat_untilt_ne_zero p (h ▸ hz)

/-- The standard primitive theta-kernel element [p^flat]-p. -/
def thetaGenerator : Logarithm.PeriodRings.AInf p := Cyclotomic.towerToAInf p (pTower p) - p

theorem thetaGenerator_theta : Logarithm.PeriodRings.theta p (thetaGenerator p) = 0 := by
  rw [thetaGenerator, map_sub, map_natCast, Cyclotomic.theta_towerToAInf]
  change (p : 𝓞_ℂ_[p]) - p = 0
  exact sub_self _

theorem thetaGenerator_coeff_zero : (thetaGenerator p).coeff 0 = pFlat p := by
  change WittVector.constantCoeff (thetaGenerator p) = _
  rw [thetaGenerator, map_sub, map_natCast]
  change (WittVector.teichmuller p (pFlat p)).coeff 0 - (p : PreTilt 𝓞_ℂ_[p] p) = pFlat p
  rw [WittVector.teichmuller_coeff_zero, CharP.cast_eq_zero, sub_zero]

theorem thetaGenerator_ne_zero : thetaGenerator p ≠ 0 := by
  intro h
  have he := congrArg (fun x : Logarithm.PeriodRings.AInf p => x.coeff 0) h
  rw [thetaGenerator_coeff_zero, WittVector.zero_coeff] at he
  exact pFlat_ne_zero p he

theorem pFlat_dvd_kernel_coeff (x : Logarithm.PeriodRings.AInf p) (hx : Logarithm.PeriodRings.theta p x = 0) :
    pFlat p ∣ x.coeff 0 := by
  have hmod : PreTilt.coeff 0 (x.coeff 0) = 0 := by
    rw [← Logarithm.PeriodRings.thetaModP_eq]
    simp only [Logarithm.PeriodRings.thetaModP, RingHom.comp_apply, hx, map_zero]
  have hmem : (x.coeff 0).untilt ∈ Ideal.span {(p : 𝓞_ℂ_[p])} :=
    Ideal.Quotient.eq_zero_iff_mem.mp ((PreTilt.mk_untilt_eq_coeff_zero _).trans hmod)
  apply tilt_dvd_of_untilt_norm_le p _ _ (pFlat_untilt_ne_zero p)
  rw [pFlat_untilt]
  have he := (Logarithm.PeriodRings.mem_p_power_iff p 1 (x.coeff 0).untilt).mp (by simpa only [pow_one] using hmem)
  change ‖((x.coeff 0).untilt : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖
  simpa only [pow_one] using he

/-- Every theta-kernel element has a first digit divisible by the concrete generator. -/
theorem theta_kernel_digit (x : Logarithm.PeriodRings.AInf p) (hx : Logarithm.PeriodRings.theta p x = 0) :
    ∃ a : Logarithm.PeriodRings.AInf p, (p : Logarithm.PeriodRings.AInf p) ∣ x - thetaGenerator p * a := by
  obtain ⟨a, ha⟩ := pFlat_dvd_kernel_coeff p x hx
  refine ⟨WittVector.teichmuller p a, ?_⟩
  rw [← Ideal.mem_span_singleton, WittVector.mem_span_p_iff_coeff_zero_eq_zero]
  change WittVector.constantCoeff (x - thetaGenerator p * WittVector.teichmuller p a) = 0
  rw [map_sub, map_mul]
  change x.coeff 0 - (thetaGenerator p).coeff 0 * (WittVector.teichmuller p a).coeff 0 = 0
  rw [thetaGenerator_coeff_zero, WittVector.teichmuller_coeff_zero, ha, sub_self]

/-- Fontaine theta has a proved principal kernel in the actual A_inf. -/
theorem theta_kernel_eq_span : RingHom.ker (Logarithm.PeriodRings.theta p) = Ideal.span {thetaGenerator p} := by
  apply le_antisymm
  · apply AdicGeneration.ideal_le_span_of_adic_step (p : Logarithm.PeriodRings.AInf p) (thetaGenerator p)
    intro x
    have hx : Logarithm.PeriodRings.theta p (x : Logarithm.PeriodRings.AInf p) = 0 := RingHom.mem_ker.mp x.property
    obtain ⟨a, b, hb⟩ := theta_kernel_digit p x hx
    have hbker : Logarithm.PeriodRings.theta p b = 0 := by
      have he := congrArg (Logarithm.PeriodRings.theta p) hb
      simp only [map_sub, map_mul, map_natCast, thetaGenerator_theta, hx, zero_mul, sub_zero] at he
      exact (mul_eq_zero.mp he.symm).resolve_left (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    refine ⟨a, ⟨b, RingHom.mem_ker.mpr hbker⟩, ?_⟩
    change (x : Logarithm.PeriodRings.AInf p) = thetaGenerator p * a + (p : Logarithm.PeriodRings.AInf p) * b
    linear_combination hb
  · apply Ideal.span_le.mpr
    intro x hx
    have he : x = thetaGenerator p := Set.mem_singleton_iff.mp hx
    subst x
    exact RingHom.mem_ker.mpr (thetaGenerator_theta p)

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaKernel
