import OAI.Analysis.Normed.Function.Holder.Banach.Composition
import OAI.Analysis.Normed.Function.Holder.Banach.Operator
import OAI.Analysis.Normed.Function.Holder.Banach.Linear
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Quantitative Hölder calculus for finite-jet expressions. Constants are chosen
before the input fields. In particular, differentiating a smooth expression in
lower jets only asks for Hölder bounds on the next jets, not their derivatives. -/

noncomputable section
open scoped BoundedContinuousFunction
namespace OAI.Analysis.Normed.Function.Holder.HolderMap

variable {X E F G : Type*} [MetricSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {α : ℝ}

def pair (a : HolderMap X E α) (b : HolderMap X F α) : HolderMap X (E × F) α :=
  HolderMap.map (ContinuousLinearMap.inl ℝ E F) a + HolderMap.map (ContinuousLinearMap.inr ℝ E F) b

@[simp] theorem value_pair (a : HolderMap X E α) (b : HolderMap X F α) (x : X) :
    HolderMap.value (HolderMap.pair a b) x = (HolderMap.value a x, HolderMap.value b x) := by
  simp [HolderMap.pair]

theorem norm_pair_le (hα : 0 ≤ α) (a : HolderMap X E α) (b : HolderMap X F α) :
    ‖HolderMap.pair a b‖ ≤ max ‖a‖ ‖b‖ := by
  apply HolderMap.norm_le_of_bounds hα (le_trans (norm_nonneg a) (le_max_left _ _))
  · intro x
    rw [HolderMap.value_pair, Prod.norm_def]
    exact max_le_max (HolderMap.norm_value_le a x) (HolderMap.norm_value_le b x)
  · intro x y
    rw [HolderMap.value_pair, HolderMap.value_pair, Prod.norm_def]
    apply max_le
    · exact (HolderMap.norm_sub_le a x y).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _))
    · exact (HolderMap.norm_sub_le b x y).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg dist_nonneg _))

theorem norm_pair_le_of_le (hα : 0 ≤ α) {a : HolderMap X E α} {b : HolderMap X F α}
    {R : ℝ} (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) : ‖HolderMap.pair a b‖ ≤ R :=
  (HolderMap.norm_pair_le hα a b).trans (max_le ha hb)

local instance sourceHolderOperatorGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance sourceHolderOperatorSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance

theorem norm_action_le_of_norm_le (hα : 0 ≤ α) {R : ℝ} (hR : 0 ≤ R)
    (a : HolderMap X (E →L[ℝ] F) α) (v : HolderMap X E α)
    (ha : ‖a‖ ≤ R) (hv : ‖v‖ ≤ R) : ‖HolderMap.action hα a v‖ ≤ 2 * R ^ 2 := by
  calc
    _ ≤ 2 * ‖a‖ * ‖v‖ := HolderMap.norm_action_le hα a v
    _ ≤ 2 * R * R := mul_le_mul (mul_le_mul_of_nonneg_left ha (by norm_num))
      hv (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- A differentiated smooth finite-jet expression has a bound depending only
on its argument and its first jet. No second derivative of the input occurs. -/
theorem exists_derivative_expression_bound [ProperSpace F]
    {Φ : F → G} (hΦ : ContDiff ℝ 2 Φ) (hα : 0 ≤ α) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : HolderMap X F α)
      (da : HolderMap X (E →L[ℝ] F) α) (v : HolderMap X E α),
      ‖a‖ ≤ R → ∃ b : HolderMap X G α,
        (∀ x, HolderMap.value b x = fderiv ℝ Φ (HolderMap.value a x) (HolderMap.value da x (HolderMap.value v x))) ∧
        ‖b‖ ≤ C * (1 + ‖a‖) * ‖da‖ * ‖v‖ := by
  have hdΦ : ContDiff ℝ 1 (fderiv ℝ Φ) := hΦ.fderiv_right (by norm_num)
  obtain ⟨C, hC, hbound⟩ := HolderMap.exists_compose_contDiff_bound (X := X) hdΦ hα hR
  refine ⟨4 * C, by positivity, ?_⟩
  intro a da v ha
  obtain ⟨D, hD, hDn⟩ := hbound a ha
  refine ⟨HolderMap.action hα D (HolderMap.action hα da v), ?_, ?_⟩
  · intro x
    simp only [HolderMap.value_action, hD]
  · calc
      ‖HolderMap.action hα D (HolderMap.action hα da v)‖ ≤ 2 * ‖D‖ * ‖HolderMap.action hα da v‖ := HolderMap.norm_action_le _ _ _
      _ ≤ 2 * (C * (1 + ‖a‖)) * (2 * ‖da‖ * ‖v‖) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hDn (by norm_num))
          (HolderMap.norm_action_le _ _ _) (norm_nonneg _) (by positivity)
      _ = _ := by ring

end OAI.Analysis.Normed.Function.Holder.HolderMap
