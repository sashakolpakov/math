import OAI.Analysis.Normed.Function.Holder.Banach.Norm
import OAI.Analysis.Normed.Function.Holder.Banach.Maps
import Mathlib.Analysis.Calculus.ContDiff.RCLike

open Set Metric
open scoped BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder.HolderMap

variable {X F G : Type*} [MetricSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {α : ℝ}

/-- A smooth finite-dimensional coefficient function takes bounded Hölder
fields to bounded Hölder fields. The norm control is uniform on each ball. -/
theorem exists_compose_contDiff_bound {f : F → G} (hf : ContDiff ℝ 1 f)
    (hα : 0 ≤ α) {R : ℝ} (_ : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : HolderMap X F α, ‖a‖ ≤ R →
      ∃ b : HolderMap X G α,
        (∀ x, HolderMap.value b x = f (HolderMap.value a x)) ∧ ‖b‖ ≤ C * (1 + ‖a‖) := by
  obtain ⟨L, hL⟩ := hf.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall (0 : F) R) (isCompact_closedBall (0 : F) R)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : F) R).exists_bound_of_continuousOn
    hf.continuous.continuousOn
  let C : ℝ := max M 0 + L
  have hC : 0 ≤ C := add_nonneg (le_max_right _ _) L.coe_nonneg
  refine ⟨C, hC, ?_⟩
  intro a ha
  have haR (x : X) : HolderMap.value a x ∈ closedBall (0 : F) R := by
    rw [mem_closedBall, dist_zero_right]
    exact (HolderMap.norm_value_le a x).trans ha
  let v : X →ᵇ G := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x ↦ f (HolderMap.value a x)) (hf.continuous.comp (HolderMap.value a).continuous) (max M 0)
    (fun x ↦ (hM _ (haR x)).trans (le_max_left _ _))
  have hv (x y : X) : ‖v x - v y‖ ≤ ((L : ℝ) * ‖a‖) * (dist x y) ^ α := by
    calc
      ‖v x - v y‖ = dist (f (HolderMap.value a x)) (f (HolderMap.value a y)) := (dist_eq_norm _ _).symm
      _ ≤ L * dist (HolderMap.value a x) (HolderMap.value a y) := hL.dist_le_mul _ (haR x) _ (haR y)
      _ ≤ L * (‖a‖ * (dist x y) ^ α) := by
        rw [dist_eq_norm]
        exact mul_le_mul_of_nonneg_left (HolderMap.norm_sub_le a x y) L.coe_nonneg
      _ = _ := by ring
  let b : HolderMap X G α := HolderMap.ofBounded hα v hv
  refine ⟨b, fun _ ↦ rfl, ?_⟩
  apply HolderMap.norm_le_of_bounds hα (mul_nonneg hC (by positivity))
  · intro x
    have hx : ‖HolderMap.value b x‖ ≤ max M 0 := (hM _ (haR x)).trans (le_max_left _ _)
    have hMC : max M 0 ≤ C := le_add_of_nonneg_right L.coe_nonneg
    exact hx.trans (hMC.trans (le_mul_of_one_le_right hC (by linarith [norm_nonneg a])))
  · intro x y
    have hLC : (L : ℝ) ≤ C := le_add_of_nonneg_left (le_max_right _ _)
    have hnorm : (L : ℝ) * ‖a‖ ≤ C * (1 + ‖a‖) :=
      (mul_le_mul_of_nonneg_right hLC (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (by linarith) hC)
    exact (hv x y).trans (mul_le_mul_of_nonneg_right hnorm (Real.rpow_nonneg dist_nonneg _))

end OAI.Analysis.Normed.Function.Holder.HolderMap
