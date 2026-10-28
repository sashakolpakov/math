import OAI.Analysis.Normed.Function.Holder.Banach.Construct

/-! Quantitative Hölder pullback by a fixed Lipschitz coordinate map. -/

noncomputable section
open scoped BoundedContinuousFunction
namespace OAI.Analysis.Normed.Function.Holder

variable {X Y F : Type*} [MetricSpace X] [MetricSpace Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {α : ℝ}

theorem exists_holder_lipschitz_pullback (hα : 0 ≤ α)
    (f : HolderMap Y F α) (g : X → Y) (hg : Continuous g)
    {L : ℝ} (hL : 0 ≤ L) (hLip : ∀ x y, dist (g x) (g y) ≤ L*dist x y) :
    ∃ P : HolderMap X F α,
      (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value P x = OAI.Analysis.Normed.Function.Holder.HolderMap.value f (g x)) ∧
      ‖P‖ ≤ max 1 (L^α)*‖f‖ := by
  let b : X →ᵇ F := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => OAI.Analysis.Normed.Function.Holder.HolderMap.value f (g x)) ((OAI.Analysis.Normed.Function.Holder.HolderMap.value f).continuous.comp hg)
    ‖f‖ (fun x => OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le f (g x))
  have hh (x y : X) : ‖b x-b y‖ ≤ (L^α*‖f‖)*dist x y^α := by
    calc
      _ ≤ ‖f‖*dist (g x) (g y)^α := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le f (g x) (g y)
      _ ≤ ‖f‖*(L*dist x y)^α := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow dist_nonneg (hLip x y) hα) (norm_nonneg f)
      _ = _ := by rw [Real.mul_rpow hL dist_nonneg]; ring
  refine ⟨OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα b hh, fun _ => rfl, ?_⟩
  apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_ofBounded_le hα b (by positivity) hh).trans
  have hbn : ‖b‖ ≤ ‖f‖ := BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
    (norm_nonneg f) _
  exact (max_le_max hbn le_rfl).trans_eq
    (by rw [max_mul_of_nonneg _ _ (norm_nonneg f), one_mul])

end OAI.Analysis.Normed.Function.Holder
