import Mathlib.Analysis.Distribution.FourierMultiplier
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section
open scoped ContDiff

namespace OAI.Analysis.Fourier.BesselPotential

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem temperate_fderiv {f : E → F} (hf : f.HasTemperateGrowth) :
    (fderiv ℝ f).HasTemperateGrowth := by
  refine ⟨(contDiff_infty_iff_fderiv.mp hf.1).2, fun n => ?_⟩
  obtain ⟨k,C,hC⟩ := hf.2 (n+1)
  refine ⟨k,C,fun x => ?_⟩
  simpa only [norm_iteratedFDeriv_fderiv] using hC x

/-- Real powers preserve temperate growth when the positive input is
uniformly separated from zero. The derivative bound is the same
one-dimensional bound used for Bessel weights in Mathlib. -/
theorem temperate_rpow_of_half_lt {f : E → ℝ} (hf : f.HasTemperateGrowth)
    (hpos : ∀ x, 1/2 < f x) (r : ℝ) :
    (fun x => (f x) ^ r).HasTemperateGrowth := by
  let t : Set ℝ := {y | 1/2 < y}
  have ht : Set.range f ⊆ t := by
    rintro _ ⟨x,rfl⟩
    exact hpos x
  have hdiff : ContDiffOn ℝ ∞ (fun x : ℝ => x^r) t :=
    contDiffOn_fun_id.rpow_const_of_ne fun x hx => (lt_trans (by norm_num) hx).ne'
  have hunique : UniqueDiffOn ℝ t := (isOpen_lt' (1/2 : ℝ)).uniqueDiffOn
  apply Function.HasTemperateGrowth.comp' ht hunique hdiff _ hf
  intro N
  obtain ⟨k,hk⟩ := exists_nat_ge (max r ((N-r)*Real.log 2/Real.log (3/2)))
  have hk₁ : r ≤ k := le_sup_left.trans hk
  have hk₂ : Real.log 2 * (N-r) ≤ Real.log (3/2) * k := by
    have := le_sup_right.trans hk
    field_simp at this
    grind
  refine ⟨k,∑ k ∈ Finset.range (N+1), ‖Polynomial.eval r (descPochhammer ℝ k)‖,
    by positivity, ?_⟩
  intro n hn x hx
  have hdx : ContDiffAt ℝ n (fun x : ℝ => x^r) x :=
    Real.contDiffAt_rpow_const (Or.inl (lt_trans (by norm_num) hx).ne')
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_eq_iteratedDeriv hunique hdx hx, iteratedDeriv_eq_iterate,
    Real.iter_deriv_rpow_const, norm_mul]
  gcongr 1
  · exact Finset.single_le_sum (f := fun k => ‖Polynomial.eval r (descPochhammer ℝ k)‖)
      (fun _ _ => by positivity)
      (show n ∈ Finset.range (N+1) by grind)
  have hx' : 1/2 < x := hx
  have hx'' : 0 < x := lt_of_lt_of_le (by norm_num) hx'.le
  simp only [Real.norm_eq_abs]
  apply (Real.abs_rpow_le_abs_rpow _ _).trans
  by_cases! h : 0 ≤ r-n
  · have hle : r-n ≤ k := by simpa using hk₁.trans (by simp)
    rw [← Real.rpow_natCast]
    exact (Real.rpow_le_rpow (by positivity) (by simp) h).trans
      (Real.rpow_le_rpow_of_exponent_le (by simp) hle)
  have h : 0 < n-r := by grind
  calc
    _ = x^(-(n-r)) := by
      rw [neg_sub]
      congr
      simpa using hx''.le
    _ ≤ (2:ℝ)^(n-r) := by
      simp only [one_div,Set.mem_ofPred_eq,t] at hx
      rw [Real.rpow_neg_eq_inv_rpow]
      gcongr
      exact ((inv_lt_comm₀ hx'' (by norm_num)).mpr hx).le
    _ = Real.exp (Real.log 2 * (n-r)) := by
      rw [Real.rpow_def_of_pos]
      norm_num
    _ ≤ Real.exp (Real.log (3/2) * k) := by
      gcongr 1
      apply le_trans _ hk₂
      gcongr
    _ ≤ (3/2)^k := by
      rw [← Real.rpow_natCast,Real.rpow_def_of_pos]
      norm_num
    _ ≤ _ := by
      gcongr
      grind

/-- The logarithm of a temperate function bounded below by one is temperate.
This follows from the genuine derivative `Df/f` and the positive power lemma. -/
theorem temperate_log_of_one_le {f : E → ℝ} (hf : f.HasTemperateGrowth)
    (hpos : ∀ x, 1 ≤ f x) :
    (fun x => Real.log (f x)).HasTemperateGrowth := by
  have hne (x : E) : f x ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (hpos x))
  have hinv : (fun x => (f x)⁻¹).HasTemperateGrowth := by
    simpa only [Real.rpow_neg_one] using
      temperate_rpow_of_half_lt hf (fun x => lt_of_lt_of_le (by norm_num) (hpos x)) (-1)
  have hd : fderiv ℝ (fun x => Real.log (f x)) =
      fun x => (f x)⁻¹ • fderiv ℝ f x := by
    funext x
    exact ((hf.1.differentiable (by simp) x).hasFDerivAt.log (hne x)).fderiv
  have hdtemp : (fderiv ℝ (fun x => Real.log (f x))).HasTemperateGrowth := by
    rw [hd]
    exact hinv.smul (temperate_fderiv hf)
  obtain ⟨k,C,hC⟩ := hf.2 0
  apply Function.HasTemperateGrowth.of_fderiv hdtemp
    (fun x => (hf.1.differentiable (by simp) x).log (hne x)) (k := k) (C := C)
  intro x
  have hx : 0 ≤ f x := (zero_le_one.trans (hpos x))
  calc
    ‖Real.log (f x)‖ = Real.log (f x) := Real.norm_of_nonneg (Real.log_nonneg (hpos x))
    _ ≤ f x := Real.log_le_self hx
    _ ≤ C * (1+‖x‖)^k := by
      simpa only [norm_iteratedFDeriv_zero,Real.norm_of_nonneg hx] using hC x

end OAI.Analysis.Fourier.BesselPotential
