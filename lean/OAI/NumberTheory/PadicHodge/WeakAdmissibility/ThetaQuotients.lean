import OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaKernel
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.AdicQuotients

/-! # Theta Quotients -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.WeakAdmissibility.ThetaQuotients

/-!
The finite theta quotients of A_inf are p-adically complete and p-torsion free.
These are proved properties of the concrete rings, not comparison assumptions.
-/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaKernel
open Filter _root_.Topology

variable (p : ℕ) [Fact p.Prime]

theorem p_dvd_thetaPower_mul (m : ℕ) (x : Logarithm.PeriodRings.AInf p)
    (hx : (p : Logarithm.PeriodRings.AInf p) ∣ ThetaKernel.thetaGenerator p ^ m * x) : (p : Logarithm.PeriodRings.AInf p) ∣ x := by
  have he : (ThetaKernel.thetaGenerator p ^ m * x).coeff 0 = 0 :=
    (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mp (Ideal.mem_span_singleton.mpr hx)
  change WittVector.constantCoeff (ThetaKernel.thetaGenerator p ^ m * x) = 0 at he
  rw [map_mul, map_pow] at he
  change (ThetaKernel.thetaGenerator p).coeff 0 ^ m * x.coeff 0 = 0 at he
  rw [ThetaKernel.thetaGenerator_coeff_zero] at he
  have hx₀ := (mul_eq_zero.mp he).resolve_left (pow_ne_zero m (ThetaKernel.pFlat_ne_zero p))
  exact Ideal.mem_span_singleton.mp ((WittVector.mem_span_p_iff_coeff_zero_eq_zero x).mpr hx₀)

theorem thetaPower_cancel_pPower (m n : ℕ) (x : Logarithm.PeriodRings.AInf p)
    (hx : ThetaKernel.thetaGenerator p ^ m * x ∈ (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) ^ n) :
    x ∈ (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) ^ n := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx ⊢
  exact AdicQuotients.pow_dvd_cancel_factor (p : Logarithm.PeriodRings.AInf p) (ThetaKernel.thetaGenerator p ^ m)
    (by exact_mod_cast (Fact.out : p.Prime).ne_zero) (p_dvd_thetaPower_mul p m) n x hx

abbrev ThetaPowerQuotient (m : ℕ) := Logarithm.PeriodRings.AInf p ⧸ Ideal.span {ThetaKernel.thetaGenerator p ^ m}

instance thetaPowerQuotient_complete (m : ℕ) :
    IsAdicComplete (Ideal.span {(p : ThetaPowerQuotient p m)}) (ThetaPowerQuotient p m) := by
  have he := AdicQuotients.quotient_isAdicComplete (p : Logarithm.PeriodRings.AInf p) (ThetaKernel.thetaGenerator p ^ m)
    (thetaPower_cancel_pPower p m)
  simpa only [map_natCast] using he

theorem thetaPowerQuotient_p_cancel (m : ℕ) (z : ThetaPowerQuotient p m)
    (hz : (p : ThetaPowerQuotient p m) * z = 0) : z = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hmem : (p : Logarithm.PeriodRings.AInf p) * a ∈ Ideal.span {ThetaKernel.thetaGenerator p ^ m} := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul, map_natCast] using hz
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hmem
  obtain ⟨c, hc⟩ := p_dvd_thetaPower_mul p m b ⟨a, hb.symm⟩
  have he : a = ThetaKernel.thetaGenerator p ^ m * c := by
    apply mul_left_cancel₀ (show (p : Logarithm.PeriodRings.AInf p) ≠ 0 by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    calc
      (p : Logarithm.PeriodRings.AInf p) * a = ThetaKernel.thetaGenerator p ^ m * b := hb
      _ = (p : Logarithm.PeriodRings.AInf p) * (ThetaKernel.thetaGenerator p ^ m * c) := by rw [hc]; ring
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ⟨c, he⟩)

theorem thetaPowerQuotient_pPower_cancel (m n : ℕ) (z : ThetaPowerQuotient p m)
    (hz : (p : ThetaPowerQuotient p m) ^ n * z = 0) : z = 0 := by
  induction n generalizing z with
  | zero => simpa only [pow_zero, one_mul] using hz
  | succ n ih =>
    apply ih
    apply thetaPowerQuotient_p_cancel p m
    have he : (p : ThetaPowerQuotient p m) * ((p : ThetaPowerQuotient p m) ^ n * z) =
        (p : ThetaPowerQuotient p m) ^ (n + 1) * z := by rw [pow_succ]; ring
    exact he.trans hz

/-- Powers of the theta ideal are saturated with respect to every power of p. -/
theorem thetaPower_p_saturated (m n : ℕ) (x : Logarithm.PeriodRings.AInf p)
    (hx : (p : Logarithm.PeriodRings.AInf p) ^ n * x ∈ Ideal.span {ThetaKernel.thetaGenerator p ^ m}) :
    x ∈ Ideal.span {ThetaKernel.thetaGenerator p ^ m} := by
  have he : (p : ThetaPowerQuotient p m) ^ n * Ideal.Quotient.mk _ x = 0 := by
    simpa only [map_mul, map_pow, map_natCast] using Ideal.Quotient.eq_zero_iff_mem.mpr hx
  exact Ideal.Quotient.eq_zero_iff_mem.mp (thetaPowerQuotient_pPower_cancel p m n _ he)

theorem untilt_eq_zero_iff (a : PreTilt 𝓞_ℂ_[p] p) : a.untilt = 0 ↔ a = 0 := by
  constructor
  · intro ha
    let e := PeriodInvariants.PeriodRing.tiltMonoidEquiv p
    let t := e.symm a
    have ht : Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 t = 0 := by
      have he := PeriodInvariants.PeriodRing.untilt_tiltMonoidEquiv p t
      change (e (e.symm a)).untilt = _ at he
      rw [e.apply_symm_apply, ha] at he
      exact he.symm
    have hcoeff (n : ℕ) : Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n t = 0 :=
      eq_zero_of_pow_eq_zero ((Perfection.coeffMonoidHom_pow_p_pow_self t n).trans ht)
    have he : e t = 0 := by
      apply Perfection.ext
      intro n
      change Ideal.Quotient.mk _ (Perfection.coeffMonoidHom 𝓞_ℂ_[p] p n t) = 0
      rw [hcoeff, map_zero]
    exact (e.apply_symm_apply a).symm.trans he
  · rintro rfl
    exact Perfection.teichmuller_zero

theorem thetaPower_coeff_norm_bound (x : Logarithm.PeriodRings.AInf p) (n : ℕ) (hx : ThetaKernel.thetaGenerator p ^ n ∣ x) :
    ‖((x.coeff 0).untilt : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ n := by
  obtain ⟨a, ha⟩ := hx
  have hcoeff : x.coeff 0 = ThetaKernel.pFlat p ^ n * a.coeff 0 := by
    have he := congrArg (WittVector.constantCoeff : Logarithm.PeriodRings.AInf p →+* PreTilt 𝓞_ℂ_[p] p) ha
    rw [map_mul, map_pow] at he
    change x.coeff 0 = (ThetaKernel.thetaGenerator p).coeff 0 ^ n * a.coeff 0 at he
    rwa [ThetaKernel.thetaGenerator_coeff_zero] at he
  have huntilt : (x.coeff 0).untilt = (p : 𝓞_ℂ_[p]) ^ n * (a.coeff 0).untilt := by
    rw [hcoeff, map_mul, map_pow, ThetaKernel.pFlat_untilt]
  have hnorm : ‖((x.coeff 0).untilt : ℂ_[p])‖ =
      ‖(p : ℂ_[p])‖ ^ n * ‖((a.coeff 0).untilt : ℂ_[p])‖ := by
    rw [huntilt]
    change ‖(p : ℂ_[p]) ^ n * ((a.coeff 0).untilt : ℂ_[p])‖ = _
    rw [norm_mul, norm_pow]
  rw [hnorm]
  exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) n)
    (Logarithm.PeriodRings.integer_norm_le_one p (a.coeff 0).untilt)

theorem coeff_zero_of_dvd_all_thetaPowers (x : Logarithm.PeriodRings.AInf p)
    (hx : ∀ n : ℕ, ThetaKernel.thetaGenerator p ^ n ∣ x) : x.coeff 0 = 0 := by
  have ht : Tendsto (fun n : ℕ => ‖(p : ℂ_[p])‖ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (Logarithm.PeriodRings.norm_p_lt_one p)
  have hle : ‖((x.coeff 0).untilt : ℂ_[p])‖ ≤ 0 :=
    ge_of_tendsto' ht (fun n => thetaPower_coeff_norm_bound p x n (hx n))
  have hz : ((x.coeff 0).untilt : ℂ_[p]) = 0 := norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
  exact (untilt_eq_zero_iff p (x.coeff 0)).mp (Subtype.ext hz)

/-- The concrete Fontaine ring is separated for the theta-adic filtration. -/
theorem eq_zero_of_dvd_all_thetaPowers (x : Logarithm.PeriodRings.AInf p)
    (hx : ∀ n : ℕ, ThetaKernel.thetaGenerator p ^ n ∣ x) : x = 0 := by
  have hfirst (y : Logarithm.PeriodRings.AInf p) (hy : ∀ n : ℕ, ThetaKernel.thetaGenerator p ^ n ∣ y) : (p : Logarithm.PeriodRings.AInf p) ∣ y :=
    Ideal.mem_span_singleton.mp ((WittVector.mem_span_p_iff_coeff_zero_eq_zero y).mpr
      (coeff_zero_of_dvd_all_thetaPowers p y hy))
  have hdiv (k : ℕ) : ∀ y : Logarithm.PeriodRings.AInf p, (∀ n : ℕ, ThetaKernel.thetaGenerator p ^ n ∣ y) → (p : Logarithm.PeriodRings.AInf p) ^ k ∣ y := by
    induction k with
    | zero => intro y _; simp
    | succ k ih =>
      intro y hy
      obtain ⟨z, hz⟩ := hfirst y hy
      have hzall (n : ℕ) : ThetaKernel.thetaGenerator p ^ n ∣ z := by
        apply Ideal.mem_span_singleton.mp
        apply thetaPower_p_saturated p n 1 z
        simpa only [pow_one, hz] using Ideal.mem_span_singleton.mpr (hy n)
      obtain ⟨w, hw⟩ := ih z hzall
      refine ⟨w, ?_⟩
      rw [hz, hw, pow_succ]
      ring
  apply IsHausdorff.haus (show IsHausdorff (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) (Logarithm.PeriodRings.AInf p) from inferInstance)
  intro n
  have hmem : x ∈ (Ideal.span {(p : Logarithm.PeriodRings.AInf p)}) ^ n := by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hdiv n x hx
  simpa only [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top] using hmem

instance thetaGenerator_adicHausdorff : IsHausdorff (Ideal.span {ThetaKernel.thetaGenerator p}) (Logarithm.PeriodRings.AInf p) where
  haus' x hx := by
    apply eq_zero_of_dvd_all_thetaPowers p x
    intro n
    rw [← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow]
    simpa only [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top] using hx n

end NumberTheory.PadicHodge.WeakAdmissibility.ThetaQuotients

namespace NumberTheory.PadicHodge.WeakAdmissibility.ThetaQuotients.TiltCompleteness

/-! Completeness of the concrete tilt for its natural principal adic filtration. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaKernel OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaQuotients
open Filter _root_.Topology
variable (p : ℕ) [Fact p.Prime]

def untiltRoot (a : PreTilt 𝓞_ℂ_[p] p) (r : ℕ) : 𝓞_ℂ_[p] :=
  Perfection.coeffMonoidHom 𝓞_ℂ_[p] p r ((PeriodInvariants.PeriodRing.tiltMonoidEquiv p).symm a)

theorem untiltRoot_zero (a : PreTilt 𝓞_ℂ_[p] p) : untiltRoot p a 0 = a.untilt := by
  have he := PeriodInvariants.PeriodRing.untilt_tiltMonoidEquiv p ((PeriodInvariants.PeriodRing.tiltMonoidEquiv p).symm a)
  rw [MulEquiv.apply_symm_apply] at he
  exact he.symm

theorem untiltRoot_pow (a : PreTilt 𝓞_ℂ_[p] p) (r : ℕ) :
    untiltRoot p a r ^ (p ^ r) = a.untilt := by
  have he := Perfection.coeffMonoidHom_pow_p_pow_self ((PeriodInvariants.PeriodRing.tiltMonoidEquiv p).symm a) r
  exact he.trans (untiltRoot_zero p a)

theorem untiltRoot_mod (a : PreTilt 𝓞_ℂ_[p] p) (r : ℕ) :
    Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p])}) (untiltRoot p a r) =
      PreTilt.coeff r a := by
  have he := congrArg (PreTilt.coeff r)
    ((PeriodInvariants.PeriodRing.tiltMonoidEquiv p).apply_symm_apply a)
  exact he

theorem untiltRoot_norm_pow (a : PreTilt 𝓞_ℂ_[p] p) (r : ℕ) :
    ‖(untiltRoot p a r : ℂ_[p])‖ ^ (p ^ r) = ‖(a.untilt : ℂ_[p])‖ := by
  rw [← norm_pow]
  have he := congrArg (fun b : 𝓞_ℂ_[p] => (b : ℂ_[p])) (untiltRoot_pow p a r)
  exact congrArg norm he

theorem untilt_norm_le_of_coeff_eq (a b : PreTilt 𝓞_ℂ_[p] p) (r : ℕ)
    (hab : PreTilt.coeff r a = PreTilt.coeff r b) :
    ‖(a.untilt : ℂ_[p])‖ ≤ max ‖(b.untilt : ℂ_[p])‖ (‖(p : ℂ_[p])‖ ^ (p ^ r)) := by
  have hd : untiltRoot p a r - untiltRoot p b r ∈ Ideal.span {(p : 𝓞_ℂ_[p])} := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, untiltRoot_mod, untiltRoot_mod, hab, sub_self]
  have hdn : ‖((untiltRoot p a r - untiltRoot p b r : 𝓞_ℂ_[p]) : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ := by
    have he := (Logarithm.PeriodRings.mem_p_power_iff p 1 _).mp (by simpa only [pow_one] using hd)
    simpa only [pow_one] using he
  have hroot : ‖(untiltRoot p a r : ℂ_[p])‖ ≤
      max ‖(untiltRoot p b r : ℂ_[p])‖ ‖(p : ℂ_[p])‖ := by
    have he : (untiltRoot p a r : ℂ_[p]) = (untiltRoot p b r : ℂ_[p]) +
        ((untiltRoot p a r - untiltRoot p b r : 𝓞_ℂ_[p]) : ℂ_[p]) := by
      change (untiltRoot p a r : ℂ_[p]) = (untiltRoot p b r : ℂ_[p]) +
        ((untiltRoot p a r : ℂ_[p]) - (untiltRoot p b r : ℂ_[p]))
      ring
    rw [he]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max le_rfl hdn)
  have hp := pow_le_pow_left₀ (norm_nonneg (untiltRoot p a r : ℂ_[p])) hroot (p ^ r)
  rcases le_total ‖(untiltRoot p b r : ℂ_[p])‖ ‖(p : ℂ_[p])‖ with h | h
  · rw [max_eq_right h, untiltRoot_norm_pow] at hp
    exact hp.trans (le_max_right _ _)
  · rw [max_eq_left h, untiltRoot_norm_pow, untiltRoot_norm_pow] at hp
    exact hp.trans (le_max_left _ _)

theorem norm_untilt_of_pFlat_dvd (a : PreTilt 𝓞_ℂ_[p] p) (n : ℕ) (ha : ThetaKernel.pFlat p ^ n ∣ a) :
    ‖(a.untilt : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ n := by
  obtain ⟨b, rfl⟩ := ha
  have he : ((PreTilt.untilt (ThetaKernel.pFlat p ^ n * b) : 𝓞_ℂ_[p]) : ℂ_[p]) =
      (p : ℂ_[p]) ^ n * (b.untilt : ℂ_[p]) := by
    rw [map_mul, map_pow, ThetaKernel.pFlat_untilt]
    rfl
  rw [he, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (Logarithm.PeriodRings.integer_norm_le_one p b.untilt)

instance tiltHausdorff : IsHausdorff (Ideal.span {ThetaKernel.pFlat p}) (PreTilt 𝓞_ℂ_[p] p) where
  haus' a ha := by
    have hn (n : ℕ) : ‖(a.untilt : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ n := by
      apply norm_untilt_of_pFlat_dvd p
      rw [← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow]
      simpa only [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top] using ha n
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (p : ℂ_[p])) (Logarithm.PeriodRings.norm_p_lt_one p)
    have hzero : ‖(a.untilt : ℂ_[p])‖ = 0 := le_antisymm (ge_of_tendsto' ht hn) (norm_nonneg _)
    apply (untilt_eq_zero_iff p a).mp
    exact Subtype.ext (norm_eq_zero.mp hzero)

theorem coeff_pFlat_power_zero (r : ℕ) :
    PreTilt.coeff r (ThetaKernel.pFlat p ^ (p ^ r)) = 0 := by
  rw [map_pow]
  change Perfection.coeffMonoidHom (ModP 𝓞_ℂ_[p] p) p r (ThetaKernel.pFlat p) ^ (p ^ r) = 0
  erw [Perfection.coeffMonoidHom_pow_p_pow_self]
  change PreTilt.coeff 0 (ThetaKernel.pFlat p) = 0
  rw [← PreTilt.mk_untilt_eq_coeff_zero, ThetaKernel.pFlat_untilt]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (Set.mem_singleton _)

theorem coeff_eq_of_pFlat_power_dvd (a b : PreTilt 𝓞_ℂ_[p] p) (r : ℕ)
    (hab : ThetaKernel.pFlat p ^ (p ^ r) ∣ a - b) :
    PreTilt.coeff r a = PreTilt.coeff r b := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  obtain ⟨c, hc⟩ := hab
  rw [hc, map_mul, coeff_pFlat_power_zero, zero_mul]

def coefficientLimit (f : ℕ → PreTilt 𝓞_ℂ_[p] p)
    (hf : ∀ {m n : ℕ}, m ≤ n → ThetaKernel.pFlat p ^ m ∣ f m - f n) : PreTilt 𝓞_ℂ_[p] p := by
  refine ⟨fun r => PreTilt.coeff r (f (p ^ r)), ?_⟩
  intro r
  change PreTilt.coeff (r + 1) (f (p ^ (r + 1))) ^ p =
    PreTilt.coeff r (f (p ^ r))
  calc
    _ = PreTilt.coeff r (f (p ^ (r + 1))) :=
      (f (p ^ (r + 1))).property r
    _ = _ := (coeff_eq_of_pFlat_power_dvd p _ _ r
      (hf (Nat.pow_le_pow_right (Fact.out : p.Prime).one_lt.le (Nat.le_succ r)))).symm

theorem coefficientLimit_coeff (f : ℕ → PreTilt 𝓞_ℂ_[p] p)
    (hf : ∀ {m n : ℕ}, m ≤ n → ThetaKernel.pFlat p ^ m ∣ f m - f n) (r : ℕ) :
    PreTilt.coeff r (coefficientLimit p f hf) =
      PreTilt.coeff r (f (p ^ r)) := rfl

theorem coefficientLimit_approx (f : ℕ → PreTilt 𝓞_ℂ_[p] p)
    (hf : ∀ {m n : ℕ}, m ≤ n → ThetaKernel.pFlat p ^ m ∣ f m - f n) (n : ℕ) :
    ThetaKernel.pFlat p ^ n ∣ f n - coefficientLimit p f hf := by
  have hn : n ≤ p ^ n := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  have he : PreTilt.coeff n (f n - coefficientLimit p f hf) =
      PreTilt.coeff n (f n - f (p ^ n)) := by
    rw [map_sub, map_sub, coefficientLimit_coeff]
  have hb := untilt_norm_le_of_coeff_eq p (f n - coefficientLimit p f hf) (f n - f (p ^ n)) n he
  have hnorm : ‖((f n - coefficientLimit p f hf).untilt : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ n :=
    hb.trans (max_le (norm_untilt_of_pFlat_dvd p _ n (hf hn))
      (pow_le_pow_of_le_one (norm_nonneg _) (Logarithm.PeriodRings.norm_p_lt_one p).le hn))
  apply ThetaKernel.tilt_dvd_of_untilt_norm_le p _ (ThetaKernel.pFlat p ^ n)
  · rw [map_pow]
    exact pow_ne_zero n (ThetaKernel.pFlat_untilt_ne_zero p)
  · have hpow : ((ThetaKernel.pFlat p ^ n).untilt : ℂ_[p]) = (p : ℂ_[p]) ^ n := by
      rw [map_pow, ThetaKernel.pFlat_untilt]
      rfl
    rwa [hpow, norm_pow]

instance tiltPrecomplete : IsPrecomplete (Ideal.span {ThetaKernel.pFlat p}) (PreTilt 𝓞_ℂ_[p] p) where
  prec' f hf := by
    have hdiv {m n : ℕ} (hmn : m ≤ n) : ThetaKernel.pFlat p ^ m ∣ f m - f n := by
      rw [← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow]
      simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using hf hmn
    refine ⟨coefficientLimit p f hdiv, fun n => ?_⟩
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact coefficientLimit_approx p f hdiv n

/-- The concrete tilt is complete at its chosen topologically nilpotent parameter. -/
instance tiltComplete : IsAdicComplete (Ideal.span {ThetaKernel.pFlat p}) (PreTilt 𝓞_ℂ_[p] p) where

end NumberTheory.PadicHodge.WeakAdmissibility.ThetaQuotients.TiltCompleteness

end

end OAI
