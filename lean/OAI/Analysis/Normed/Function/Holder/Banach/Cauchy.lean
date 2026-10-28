import OAI.Analysis.Normed.Function.Holder.Banach.Interpolation
import Mathlib.Topology.MetricSpace.Cauchy

open Set Filter Metric
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder.HolderMap

variable {X F : Type*} [MetricSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ}

/-- Uniformly bounded Hölder functions which are Cauchy in the supremum
norm are Cauchy in the lower Hölder norm. -/
theorem cauchySeq_lowerHalf (hα : 0 ≤ α) (f : ℕ → HolderMap X F α)
    {M : ℝ} (_ : 0 ≤ M) (hf : ∀ n, ‖f n‖ ≤ M)
    (hv : CauchySeq (fun n ↦ HolderMap.value (f n))) :
    CauchySeq (fun n ↦ HolderMap.lowerHalf hα (f n)) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hc : Continuous (fun t : ℝ ↦ max t (Real.sqrt (2 * t * (2 * M)))) := by fun_prop
  have ht : Tendsto (fun t : ℝ ↦ max t (Real.sqrt (2 * t * (2 * M)))) (𝓝 0) (𝓝 0) := by
    simpa using hc.tendsto 0
  have hs : ∀ᶠ t : ℝ in 𝓝 0, max t (Real.sqrt (2 * t * (2 * M))) < ε := by
    exact ht.eventually (Iio_mem_nhds hε)
  obtain ⟨δ, hδ, hsmall⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hv δ hδ
  refine ⟨N, ?_⟩
  intro m hm n hn
  let g := f m - f n
  have hg : ‖g‖ ≤ 2 * M := (_root_.norm_sub_le _ _).trans (by linarith [hf m, hf n])
  have hvg : ‖HolderMap.value g‖ < δ := by
    change ‖HolderMap.value (f m) - HolderMap.value (f n)‖ < δ
    simpa only [dist_eq_norm] using hN m hm n hn
  have hnear : ‖HolderMap.value g‖ ∈ ball (0 : ℝ) δ := by
    simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_norm] using hvg
  have hbound : ‖HolderMap.lowerHalf hα g‖ ≤ max ‖HolderMap.value g‖ (Real.sqrt (2 * ‖HolderMap.value g‖ * (2 * M))) := by
    apply (HolderMap.norm_lowerHalf_le hα g).trans
    apply max_le_max le_rfl
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hg (by positivity))
  have heq : HolderMap.lowerHalf hα g = HolderMap.lowerHalf hα (f m) - HolderMap.lowerHalf hα (f n) :=
    (HolderMap.lowerHalfCLM hα).map_sub (f m) (f n)
  rw [dist_eq_norm, ← heq]
  exact hbound.trans_lt (hsmall hnear)

/-- The lower-Hölder limit represents the given uniform limit, rather
than an unrelated function selected from completeness. -/
theorem exists_lowerHalf_limit [CompleteSpace F]
    (hα : 0 ≤ α) (f : ℕ → HolderMap X F α) {M : ℝ}
    (hM : 0 ≤ M) (hf : ∀ n, ‖f n‖ ≤ M) (v : X →ᵇ F)
    (hv : Tendsto (fun n ↦ HolderMap.value (f n)) atTop (𝓝 v)) :
    ∃ g : HolderMap X F (α / 2),
      Tendsto (fun n ↦ HolderMap.lowerHalf hα (f n)) atTop (𝓝 g) ∧ HolderMap.value g = v := by
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete
    (HolderMap.cauchySeq_lowerHalf hα f hM hf hv.cauchySeq)
  refine ⟨g, hg, ?_⟩
  have hval := ((HolderMap.valueCLM (X := X) (F := F) (α := α / 2)).continuous.tendsto g).comp hg
  exact tendsto_nhds_unique hval hv

end OAI.Analysis.Normed.Function.Holder.HolderMap
