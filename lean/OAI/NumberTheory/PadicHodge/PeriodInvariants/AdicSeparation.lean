import OAI.NumberTheory.PadicHodge.PeriodInvariants.ThetaKernel
import OAI.NumberTheory.PadicHodge.PeriodInvariants.Nontriviality

/-! # Adic Separation -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicSeparation

noncomputable section

/-!
# Separation for the theta generator

The tilt is separated for the compatible roots of p. Reduction modulo p,
together with cancellation in A_inf, lifts separation to the theta generator
and preserves it after p is inverted.
-/

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing.TiltDivisibility OAI.NumberTheory.PadicHodge.PeriodInvariants.ThetaKernel OAI.NumberTheory.PadicHodge.PeriodInvariants.Nontriviality

variable (p : ℕ) [Fact p.Prime]

theorem untilt_eq_zero (x : PreTilt 𝓞_ℂ_[p] p) (hx : x.untilt = 0) : x = 0 := by
  obtain ⟨y, rfl⟩ := (PeriodRing.tiltMonoidEquiv p).surjective x
  rw [PeriodRing.untilt_tiltMonoidEquiv] at hx
  have hy (n : ℕ) : y.val n = 0 := by
    apply Subtype.val_injective
    apply eq_zero_of_pow_eq_zero (n := p ^ n)
    rw [PeriodRing.TiltDivisibility.coefficient_pow_complex]
    exact congrArg (fun a : 𝓞_ℂ_[p] => (a : ℂ_[p])) hx
  apply Perfection.ext
  intro n
  change Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p])}) (y.val n) = 0
  rw [hy, map_zero]

theorem tilt_eq_zero_of_all_pTilt_dvd (x : PreTilt 𝓞_ℂ_[p] p)
    (hx : ∀ n : ℕ, PeriodRing.TiltDivisibility.pTilt p ^ n ∣ x) : x = 0 := by
  apply untilt_eq_zero p x
  apply IsHausdorff.haus' (I := Ideal.span {(p : 𝓞_ℂ_[p])})
  intro n
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨a, ha⟩ := hx n
  refine ⟨a.untilt, ?_⟩
  rw [ha, map_mul, map_pow, PeriodRing.TiltDivisibility.pTilt_untilt]

theorem xi_pow_dvd_of_p_mul (n : ℕ) (a : PeriodRing.Ainf p)
    (h : ThetaKernel.xi p ^ n ∣ (p : PeriodRing.Ainf p) * a) : ThetaKernel.xi p ^ n ∣ a := by
  obtain ⟨b, hb⟩ := h
  have hc : b.coeff 0 = 0 := by
    have he := congrArg (WittVector.constantCoeff (p := p)) hb
    rw [map_mul, map_mul, map_pow] at he
    change (p : PeriodRing.Ainf p).coeff 0 * a.coeff 0 = (ThetaKernel.xi p).coeff 0 ^ n * b.coeff 0 at he
    rw [WittVector.coeff_p_zero, zero_mul, ThetaKernel.xi_coeff_zero] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (pow_ne_zero n (ThetaKernel.pTilt_ne_zero p))
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp
    ((WittVector.mem_span_p_iff_coeff_zero_eq_zero b).mpr hc)
  refine ⟨c, ?_⟩
  apply mul_left_cancel₀ (show (p : PeriodRing.Ainf p) ≠ 0 from Nat.cast_ne_zero.mpr
    (Fact.out : p.Prime).ne_zero)
  rw [hb, hc]
  ring

theorem xi_pow_dvd_of_p_pow_mul (n m : ℕ) (a : PeriodRing.Ainf p)
    (h : ThetaKernel.xi p ^ n ∣ (p : PeriodRing.Ainf p) ^ m * a) : ThetaKernel.xi p ^ n ∣ a := by
  induction m with
  | zero => simpa only [pow_zero, one_mul] using h
  | succ m ih =>
    apply ih
    apply xi_pow_dvd_of_p_mul p n
    simpa only [pow_succ', mul_assoc] using h

theorem coeff_zero_of_all_xi_dvd (x : PeriodRing.Ainf p) (hx : ∀ n : ℕ, ThetaKernel.xi p ^ n ∣ x) :
    x.coeff 0 = 0 := by
  apply tilt_eq_zero_of_all_pTilt_dvd p
  intro n
  obtain ⟨a, ha⟩ := hx n
  refine ⟨a.coeff 0, ?_⟩
  have he := congrArg (WittVector.constantCoeff (p := p)) ha
  rw [map_mul, map_pow] at he
  change x.coeff 0 = (ThetaKernel.xi p).coeff 0 ^ n * a.coeff 0 at he
  rwa [ThetaKernel.xi_coeff_zero] at he

theorem ainf_eq_zero_of_all_xi_dvd (x : PeriodRing.Ainf p) (hx : ∀ n : ℕ, ThetaKernel.xi p ^ n ∣ x) : x = 0 := by
  have hp : ∀ m : ℕ, (p : PeriodRing.Ainf p) ^ m ∣ x := by
    intro m
    induction m with
    | zero => simp only [pow_zero, one_dvd]
    | succ m ih =>
      obtain ⟨a, ha⟩ := ih
      have hac : a.coeff 0 = 0 := coeff_zero_of_all_xi_dvd p a (fun n =>
        xi_pow_dvd_of_p_pow_mul p n m a (ha ▸ hx n))
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp
        ((WittVector.mem_span_p_iff_coeff_zero_eq_zero a).mpr hac)
      exact ⟨b, by rw [ha, hb, pow_succ, mul_assoc]⟩
  apply IsHausdorff.haus' (I := Ideal.span {(p : PeriodRing.Ainf p)})
  intro n
  simpa only [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton] using hp n

instance ainf_xi_separated : IsHausdorff (Ideal.span {ThetaKernel.xi p}) (PeriodRing.Ainf p) := by
  constructor
  intro x hx
  apply ainf_eq_zero_of_all_xi_dvd p x
  intro n
  simpa only [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton] using hx n

theorem binf_eq_zero_of_all_xi_dvd (x : Nontriviality.Binf p)
    (hx : ∀ n : ℕ, algebraMap (PeriodRing.Ainf p) (Nontriviality.Binf p) (ThetaKernel.xi p) ^ n ∣ x) : x = 0 := by
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (p : PeriodRing.Ainf p)) x
  have ha : a = 0 := by
    apply ainf_eq_zero_of_all_xi_dvd p a
    intro n
    have hn : IsLocalization.mk' (Nontriviality.Binf p) a s ∈
        (Ideal.span {ThetaKernel.xi p ^ n}).map (algebraMap (PeriodRing.Ainf p) (Nontriviality.Binf p)) := by
      simpa only [Ideal.map_span, Set.image_singleton, map_pow,
        Ideal.mem_span_singleton] using hx n
    obtain ⟨r, hr, har⟩ :=
      (IsLocalization.mk'_mem_map_algebraMap_iff (Submonoid.powers (p : PeriodRing.Ainf p))
        (Nontriviality.Binf p) (Ideal.span {ThetaKernel.xi p ^ n}) a s).mp hn
    obtain ⟨m, rfl⟩ := (Submonoid.mem_powers_iff r (p : PeriodRing.Ainf p)).mp hr
    exact xi_pow_dvd_of_p_pow_mul p n m a (Ideal.mem_span_singleton.mp har)
  change IsLocalization.mk' (Nontriviality.Binf p) a s = 0
  rw [ha, IsLocalization.mk'_zero]

instance binf_xi_separated :
    IsHausdorff (Ideal.span {algebraMap (PeriodRing.Ainf p) (Nontriviality.Binf p) (ThetaKernel.xi p)}) (Nontriviality.Binf p) := by
  constructor
  intro x hx
  apply binf_eq_zero_of_all_xi_dvd p x
  intro n
  simpa only [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton] using hx n

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicSeparation
