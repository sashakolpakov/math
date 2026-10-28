import Mathlib

/-! # Real Character -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.RealCharacter.Construction

noncomputable section

section

/-! Smoothness of continuous additive characters of the real line,
proved using an antiderivative and the character equation. -/

open _root_.MeasureTheory
open scoped _root_.Topology ContDiff BigOperators

theorem continuous_real_character_hasDerivAt
    (ψ : AddChar ℝ ℂ) (hψ : Continuous (fun t : ℝ => ψ t)) :
    ∃ c : ℂ, ∀ t : ℝ, HasDerivAt (fun t : ℝ => ψ t) (c * ψ t) t := by
  let J : ℝ → ℂ := fun a => ∫ t in 0..a, ψ t
  have hJ (a : ℝ) : HasDerivAt J (ψ a) a :=
    intervalIntegral.integral_hasDerivAt_right (hψ.intervalIntegrable 0 a)
      hψ.aestronglyMeasurable.stronglyMeasurableAtFilter hψ.continuousAt
  obtain ⟨a, ha⟩ : ∃ a : ℝ, J a ≠ 0 := by
    by_contra! h
    have heq : J = fun _ => 0 := funext h
    have hh := hJ 0
    rw [heq] at hh
    have hbad := hh.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
    simp only [ψ.map_zero_eq_one, one_ne_zero] at hbad
  have hformula (t : ℝ) : ψ t = (J (t + a) - J t) / J a := by
    have hint : J (t + a) - J t = ∫ s in t..t + a, ψ s := by
      have hh : J t + (∫ s in t..t + a, ψ s) = J (t + a) :=
        intervalIntegral.integral_add_adjacent_intervals
          (hψ.intervalIntegrable 0 t) (hψ.intervalIntegrable t (t + a))
      linear_combination -hh
    have hshift : (∫ s in t..t + a, ψ s) = ψ t * J a := by
      calc
        _ = ∫ s in 0..a, ψ (t + s) := by
          simpa only [add_zero] using
            (intervalIntegral.integral_comp_add_left (a := 0) (b := a) (fun s : ℝ => ψ s) t).symm
        _ = ψ t * J a := by
          simp_rw [ψ.map_add_eq_mul]
          rw [intervalIntegral.integral_const_mul]
    rw [hint, hshift, mul_div_cancel_right₀ _ ha]
  refine ⟨(ψ a - 1) / J a, fun t => ?_⟩
  have hd : HasDerivAt (fun t => (J (t + a) - J t) / J a)
      ((ψ (t + a) - ψ t) / J a) t := by
    simpa only [one_smul, Function.comp_apply, Pi.sub_apply, id_eq] using
      (((hJ (t + a)).scomp t ((hasDerivAt_id t).add_const a)).sub
        (hJ t)).div_const (J a)
  have hcoef : (ψ (t + a) - ψ t) / J a =
      (ψ a - 1) / J a * ψ t := by
    rw [ψ.map_add_eq_mul]
    ring
  convert hd using 1
  · exact funext hformula
  · exact hcoef.symm

theorem continuous_real_character_exponential
    (ψ : AddChar ℝ ℂ) (hψ : Continuous (fun t : ℝ => ψ t)) :
    ∃ c : ℂ, ∀ t : ℝ, ψ t = Complex.exp ((t : ℂ) * c) := by
  obtain ⟨c, hc⟩ := continuous_real_character_hasDerivAt ψ hψ
  let f : ℝ → ℂ := fun t => ψ t * Complex.exp (-(t : ℂ) * c)
  have hf (t : ℝ) : HasDerivAt f 0 t := by
    have he : HasDerivAt (fun t : ℝ => Complex.exp (-(t : ℂ) * c))
        (Complex.exp (-(t : ℂ) * c) * (-c)) t := by
      convert (((hasDerivAt_id t).ofReal_comp.neg).mul_const c).cexp using 1 <;> simp
    have hz : c * ψ t * Complex.exp (-(t : ℂ) * c) +
        ψ t * (Complex.exp (-(t : ℂ) * c) * (-c)) = 0 := by ring
    simpa only [hz, Pi.mul_def] using (hc t).mul he
  have hconst (t : ℝ) : f t = 1 := by
    have hh := is_const_of_deriv_eq_zero (fun t => (hf t).differentiableAt)
      (fun t => (hf t).deriv) t 0
    simpa [f] using hh
  refine ⟨c, fun t => ?_⟩
  have hh := congrArg (fun z => z * Complex.exp ((t : ℂ) * c)) (hconst t)
  dsimp only [f] at hh
  rw [mul_assoc, ← Complex.exp_add] at hh
  have he : -(t : ℂ) * c + (t : ℂ) * c = 0 := by ring
  simpa only [he, Complex.exp_zero, mul_one, one_mul] using hh

theorem continuous_unitary_real_character_temperate
    (ψ : AddChar ℝ ℂ) (hψ : Continuous (fun t : ℝ => ψ t))
    (hunit : ∀ t, ‖ψ t‖ = 1) : Function.HasTemperateGrowth (fun t : ℝ => ψ t) := by
  obtain ⟨c, hc⟩ := continuous_real_character_exponential ψ hψ
  have heq : (fun t : ℝ => ψ t) = (fun t : ℝ => Complex.exp ((t : ℂ) * c)) := funext hc
  have hdiff : ContDiff ℝ ∞ (fun t : ℝ => ψ t) := by
    rw [heq]
    exact (Complex.ofRealCLM.contDiff.mul contDiff_const).cexp
  have hderiv (t : ℝ) : HasDerivAt (fun t : ℝ => ψ t) (ψ t * c) t := by
    rw [heq, hc]
    convert ((hasDerivAt_id t).ofReal_comp.mul_const c).cexp using 1 <;> simp
  have hiter (n : ℕ) : iteratedDeriv n (fun t : ℝ => ψ t) = fun t => c ^ n * ψ t := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [iteratedDeriv_succ, ih]
        funext t
        rw [((hderiv t).const_mul (c ^ n)).deriv]
        rw [pow_succ]
        ring
  refine ⟨hdiff, fun n => ⟨0, ‖c‖ ^ n, fun t => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hiter]
  simp [norm_pow, hunit]

theorem continuous_unitary_coordinate_character_temperate
    {r : ℕ} (ψ : AddChar (Fin r → ℝ) ℂ)
    (hψ : Continuous (fun x : Fin r → ℝ => ψ x))
    (hunit : ∀ x, ‖ψ x‖ = 1) : Function.HasTemperateGrowth (fun x : Fin r → ℝ => ψ x) := by
  classical
  have hsingle (i : Fin r) :
      Function.HasTemperateGrowth (fun x : Fin r → ℝ => ψ (Pi.single i (x i))) := by
    let φ : AddChar ℝ ℂ :=
      { toFun := fun t => ψ (Pi.single i t)
        map_zero_eq_one' := by simp
        map_add_eq_mul' := by
          intro s t
          rw [Pi.single_add, ψ.map_add_eq_mul] }
    have hc : Continuous (fun t : ℝ => φ t) := by
      apply hψ.comp
      apply continuous_pi
      intro j
      by_cases h : j = i
      · subst j
        simp only [Pi.single_eq_same]
        fun_prop
      · simpa [Pi.single_eq_of_ne h] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
    have ht := continuous_unitary_real_character_temperate φ hc (fun t => hunit _)
    exact ht.comp (ContinuousLinearMap.proj i : (Fin r → ℝ) →L[ℝ] ℝ).hasTemperateGrowth
  have hsum (s : Finset (Fin r)) :
      Function.HasTemperateGrowth (fun x : Fin r → ℝ => ψ (∑ i ∈ s, Pi.single i (x i))) := by
    induction s using Finset.induction_on with
    | empty =>
        simp only [Finset.sum_empty, ψ.map_zero_eq_one]
        exact Function.HasTemperateGrowth.const 1
    | @insert i s hi ih =>
        simpa only [Finset.sum_insert hi, ψ.map_add_eq_mul, Pi.mul_def] using (hsingle i).mul ih
  simpa only [Finset.univ_sum_single] using hsum Finset.univ

end

/-! Continuous unitary characters in arbitrary real field coordinates. -/

theorem real_coordinate_character_frequency
    {F : Type} [NormedField F] (e : ℝ ≃+* F) (he : Continuous e)
    (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x))
    (hu : ∀ x : F, ‖ψ x‖ = 1) (hn : ∃ x : F, ψ x ≠ 1) :
    ∃ t : ℝ, t ≠ 0 ∧ ∀ x : F, ψ x = Complex.exp (Complex.I * t * (e.symm x : ℂ)) := by
  let χ := ψ.compAddMonoidHom e.toAddEquiv.toAddMonoidHom
  obtain ⟨z, hz⟩ := continuous_real_character_exponential χ (hc.comp he)
  have hre : z.re = 0 := by
    have hh := hu (e 1)
    change ‖χ 1‖ = 1 at hh
    rw [hz] at hh
    simpa only [Complex.ofReal_one, one_mul, Complex.norm_exp, Real.exp_eq_one_iff] using hh
  have hzform : z = Complex.I * (z.im : ℂ) := by
    apply Complex.ext <;> simp [hre]
  have hψ (x : F) : ψ x = Complex.exp (Complex.I * z.im * (e.symm x : ℂ)) := by
    have hh := hz (e.symm x)
    change ψ (e (e.symm x)) = Complex.exp ((e.symm x : ℂ) * z) at hh
    rw [e.apply_symm_apply, hzform] at hh
    simpa only [mul_comm (e.symm x : ℂ), mul_assoc] using hh
  refine ⟨z.im, ?_, hψ⟩
  intro hz0
  obtain ⟨x, hx⟩ := hn
  apply hx
  rw [hψ, hz0]
  simp

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.RealCharacter.Construction
