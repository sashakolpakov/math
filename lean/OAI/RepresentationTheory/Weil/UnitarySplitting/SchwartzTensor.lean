import OAI.RepresentationTheory.Weil.UnitarySplitting.RealFourier

/-! # Schwartz Tensor -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.SchwartzTensor.Construction

noncomputable section

section

/-! External products of real Schwartz functions, with explicit decay bounds. -/

open scoped SchwartzMap ContDiff

theorem iteratedFDeriv_comp_contraction_le
    {V W Z : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (L : V →L[ℝ] W) (hL : ‖L‖ ≤ 1) (f : W → Z) (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ n f (L x)‖ := by
  rw [L.iteratedFDeriv_comp_right hf x (by exact_mod_cast le_top)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  apply mul_le_of_le_one_right (norm_nonneg _)
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => hL)

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem schwartzTensor_derivative_bound (f : SchwartzMap V ℂ) (g : SchwartzMap W ℂ)
    (n : ℕ) (x : V × W) :
    ‖iteratedFDeriv ℝ n (fun z : V × W => f z.1 * g z.2) x‖ ≤
      ‖ContinuousLinearMap.mul ℝ ℂ‖ * ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x.1‖ * ‖iteratedFDeriv ℝ (n - i) g x.2‖ := by
  have hb := (ContinuousLinearMap.mul ℝ ℂ).norm_iteratedFDeriv_le_of_bilinear
    ((f.smooth ⊤).comp contDiff_fst) ((g.smooth ⊤).comp contDiff_snd) x
    (n := n) (by exact_mod_cast le_top)
  apply hb.trans
  gcongr with i hi
  · exact iteratedFDeriv_comp_contraction_le (ContinuousLinearMap.fst ℝ V W)
      (ContinuousLinearMap.norm_fst_le ..) f (f.smooth ⊤) i x
  · exact iteratedFDeriv_comp_contraction_le (ContinuousLinearMap.snd ℝ V W)
      (ContinuousLinearMap.norm_snd_le ..) g (g.smooth ⊤) (n - i) x

theorem schwartzTensor_weighted_derivative_product (f : SchwartzMap V ℂ) (g : SchwartzMap W ℂ)
    (k i j : ℕ) (x : V × W) :
    ‖x‖ ^ k * (‖iteratedFDeriv ℝ i f x.1‖ * ‖iteratedFDeriv ℝ j g x.2‖) ≤
      SchwartzMap.seminorm ℝ k i f * SchwartzMap.seminorm ℝ 0 j g +
      SchwartzMap.seminorm ℝ 0 i f * SchwartzMap.seminorm ℝ k j g := by
  rcases le_total ‖x.2‖ ‖x.1‖ with hx | hx
  · rw [Prod.norm_def, max_eq_left hx, ← mul_assoc]
    apply (mul_le_mul (SchwartzMap.le_seminorm ℝ k i f x.1)
      (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ g j x.2) (norm_nonneg _) (apply_nonneg _ _)).trans
    exact le_add_of_nonneg_right (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
  · rw [Prod.norm_def, max_eq_right hx, mul_left_comm]
    apply (mul_le_mul (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ f i x.1)
      (SchwartzMap.le_seminorm ℝ k j g x.2) (by positivity) (apply_nonneg _ _)).trans
    exact le_add_of_nonneg_left (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _))

def schwartzTensor (f : SchwartzMap V ℂ) (g : SchwartzMap W ℂ) : SchwartzMap (V × W) ℂ where
  toFun x := f x.1 * g x.2
  smooth' := ((f.smooth ⊤).comp contDiff_fst).mul ((g.smooth ⊤).comp contDiff_snd)
  decay' k n := by
    refine ⟨‖ContinuousLinearMap.mul ℝ ℂ‖ * ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * (SchwartzMap.seminorm ℝ k i f * SchwartzMap.seminorm ℝ 0 (n - i) g +
        SchwartzMap.seminorm ℝ 0 i f * SchwartzMap.seminorm ℝ k (n - i) g), ?_⟩
    intro x
    apply (mul_le_mul_of_nonneg_left (schwartzTensor_derivative_bound f g n x) (by positivity)).trans
    rw [mul_left_comm, Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg (ContinuousLinearMap.mul ℝ ℂ))
    apply Finset.sum_le_sum
    intro i hi
    rw [mul_assoc (n.choose i : ℝ), mul_left_comm]
    exact mul_le_mul_of_nonneg_left (schwartzTensor_weighted_derivative_product f g k i (n - i) x) (by positivity)

theorem schwartzTensor_apply (f : SchwartzMap V ℂ) (g : SchwartzMap W ℂ) (x : V × W) :
    schwartzTensor f g x = f x.1 * g x.2 := rfl

end

section

/-! Schwartz slices and uniform estimates in both sets of variables. -/

open _root_.MeasureTheory
open scoped SchwartzMap ContDiff

variable {V W Z : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

def schwartzSlice (f : SchwartzMap (V × W) Z) (q : V) : SchwartzMap W Z :=
  SchwartzMap.compCLMOfAntilipschitz ℝ (g := fun y : W => (q, y))
    (by
      convert (Function.HasTemperateGrowth.const (q, 0)).add
        (ContinuousLinearMap.inr ℝ V W).hasTemperateGrowth using 1
      funext y
      simp only [Pi.add_apply, ContinuousLinearMap.inr_apply, Prod.mk_add_mk, zero_add, add_zero])
    (show AntilipschitzWith 1 (fun y : W => (q, y)) from by
      apply AntilipschitzWith.of_le_mul_dist
      intro x y
      simp only [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg : 0 ≤ dist x y),
        NNReal.coe_one, one_mul, le_refl]) f

theorem schwartzSlice_apply (f : SchwartzMap (V × W) Z) (q : V) (y : W) :
    schwartzSlice f q y = f (q, y) := rfl

theorem schwartzSlice_derivative_bound (f : SchwartzMap (V × W) Z) (q : V) (y : W) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (schwartzSlice f q) y‖ ≤ ‖iteratedFDeriv ℝ n f (q, y)‖ := by
  have hi : ‖ContinuousLinearMap.inr ℝ V W‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y
    simp only [ContinuousLinearMap.inr_apply, Prod.norm_def, norm_zero,
      max_eq_right (norm_nonneg y), one_mul, le_refl]
  change ‖iteratedFDeriv ℝ n (fun y : W => f (q, y)) y‖ ≤ _
  have h := iteratedFDeriv_comp_contraction_le (ContinuousLinearMap.inr ℝ V W)
    hi (fun x : V × W => f ((q, 0) + x))
    ((f.smooth ⊤).comp (contDiff_const.add contDiff_id)) n y
  simpa only [ContinuousLinearMap.inr_apply, Prod.mk_add_mk, zero_add, add_zero,
    iteratedFDeriv_comp_add_left, Function.comp_def] using h

theorem schwartzSlice_weighted_derivative_bound (f : SchwartzMap (V × W) Z)
    (k l n : ℕ) (q : V) (y : W) :
    ‖q‖ ^ k * (‖y‖ ^ l * ‖iteratedFDeriv ℝ n (schwartzSlice f q) y‖) ≤
      SchwartzMap.seminorm ℝ (k + l) n f := by
  apply le_trans _ (SchwartzMap.le_seminorm ℝ (k + l) n f (q, y))
  rw [pow_add, mul_assoc]
  gcongr
  · exact norm_fst_le (q, y)
  · exact norm_snd_le (q, y)
  · exact schwartzSlice_derivative_bound f q y n

theorem schwartzSlice_weighted_seminorm_bound (f : SchwartzMap (V × W) Z)
    (k l n : ℕ) (q : V) :
    ‖q‖ ^ k * SchwartzMap.seminorm ℝ l n (schwartzSlice f q) ≤
      SchwartzMap.seminorm ℝ (k + l) n f := by
  by_cases hq : ‖q‖ ^ k = 0
  · rw [hq, zero_mul]
    exact apply_nonneg _ _
  · have hqp : 0 < ‖q‖ ^ k := lt_of_le_of_ne (by positivity) (Ne.symm hq)
    rw [← le_div_iff₀' hqp]
    apply SchwartzMap.seminorm_le_bound ℝ l n _ (by positivity)
    intro y
    rw [le_div_iff₀' hqp]
    exact schwartzSlice_weighted_derivative_bound f k l n q y

theorem schwartzSlice_integrable_uniform_bound [MeasurableSpace W]
    (μ : Measure W) [μ.HasTemperateGrowth] (f : SchwartzMap (V × W) Z) :
    ∃ b : W → ℝ, Integrable b μ ∧ ∀ q y, ‖f (q, y)‖ ≤ b y := by
  let C₁ := SchwartzMap.seminorm ℝ 0 0 f
  let C₂ := SchwartzMap.seminorm ℝ μ.integrablePower 0 f
  refine ⟨fun y => (2 : ℝ) ^ μ.integrablePower * (C₁ + C₂) * (1 + ‖y‖) ^ (-(μ.integrablePower : ℝ)),
    (Measure.integrable_pow_neg_integrablePower μ).const_mul _, ?_⟩
  intro q y
  have h₁ : ‖f (q, y)‖ ≤ C₁ := SchwartzMap.norm_le_seminorm ℝ f (q, y)
  have h₂ : ‖y‖ ^ (0 + μ.integrablePower) * ‖f (q, y)‖ ≤ C₂ := by
    have h := schwartzSlice_weighted_derivative_bound f 0 μ.integrablePower 0 q y
    simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero, schwartzSlice_apply, zero_add] using h
  simpa only [pow_zero, one_mul] using
    (pow_mul_le_of_le_of_pow_mul_le (norm_nonneg y) (norm_nonneg (f (q, y))) h₁ h₂)

end

/-! Uniform decay of continuous Schwartz operators applied to slices. -/

open scoped SchwartzMap NNReal

variable {V W Z Y : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem schwartzSliceOperator_mixed_decay
    (T : SchwartzMap W Z →L[ℝ] SchwartzMap W Y) (f : SchwartzMap (V × W) Z)
    (k l n : ℕ) :
    ∃ C : ℝ, ∀ q p, ‖q‖ ^ k * (‖p‖ ^ l * ‖iteratedFDeriv ℝ n (T (schwartzSlice f q)) p‖) ≤ C := by
  let P := schwartzSeminormFamily ℝ W Z
  let R : Seminorm ℝ (SchwartzMap W Z) := (SchwartzMap.seminorm ℝ l n).comp T.toLinearMap
  have hRc : Continuous R := ((schwartz_withSeminorms ℝ W Y).continuous_seminorm (l, n)).comp T.continuous
  obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ W Z) R hRc
  refine ⟨(C : ℝ) * ∑ i ∈ s, SchwartzMap.seminorm ℝ (k + i.1) i.2 f, ?_⟩
  intro q p
  have hsup : s.sup P (schwartzSlice f q) ≤ ∑ i ∈ s, P i (schwartzSlice f q) := by
    simpa only [sum_apply] using
      Seminorm.le_def.mp (Seminorm.finset_sup_le_sum P s) (schwartzSlice f q)
  have hT : SchwartzMap.seminorm ℝ l n (T (schwartzSlice f q)) ≤
      (C : ℝ) * ∑ i ∈ s, P i (schwartzSlice f q) :=
    (Seminorm.le_def.mp hC (schwartzSlice f q)).trans (mul_le_mul_of_nonneg_left hsup C.coe_nonneg)
  apply (mul_le_mul_of_nonneg_left ((SchwartzMap.le_seminorm ℝ l n (T (schwartzSlice f q)) p).trans hT)
    (by positivity)).trans
  rw [mul_left_comm, Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
  exact Finset.sum_le_sum fun i _ => schwartzSlice_weighted_seminorm_bound f k i.1 i.2 q

theorem schwartzSliceOperator_decay
    (T : SchwartzMap W Z →L[ℝ] SchwartzMap W Y) (f : SchwartzMap (V × W) Z)
    (k : ℕ) : ∃ C : ℝ, ∀ x : V × W, ‖x‖ ^ k * ‖T (schwartzSlice f x.1) x.2‖ ≤ C := by
  obtain ⟨C₁, h₁⟩ := schwartzSliceOperator_mixed_decay T f k 0 0
  obtain ⟨C₂, h₂⟩ := schwartzSliceOperator_mixed_decay T f 0 k 0
  refine ⟨max C₁ C₂, fun x => ?_⟩
  rcases le_total ‖x.2‖ ‖x.1‖ with hx | hx
  · rw [Prod.norm_def, max_eq_left hx]
    have hh : ‖x.1‖ ^ k * ‖T (schwartzSlice f x.1) x.2‖ ≤ C₁ := by
      simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero] using h₁ x.1 x.2
    exact hh.trans (le_max_left _ _)
  · rw [Prod.norm_def, max_eq_right hx]
    have hh : ‖x.2‖ ^ k * ‖T (schwartzSlice f x.1) x.2‖ ≤ C₂ := by
      simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero] using h₂ x.1 x.2
    exact hh.trans (le_max_right _ _)

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.SchwartzTensor.Construction
