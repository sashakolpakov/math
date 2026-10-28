import OAI.Analysis.PDE.Schauder.Calculus.Schauder.DifferenceLimit

/-! Only sufficiently small nonzero difference steps are needed in the bootstrap. -/

noncomputable section
open Set Filter Metric
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Weak

theorem directional_derivative_C2_of_local_schauder_bound {m : ℕ} {α M δ : ℝ}
    (hα : 0 < α) (hδ : 0 < δ)
    (u χ : EuclideanSpace ℝ (Fin m) → ℝ) (hu : Differentiable ℝ u)
    (v : EuclideanSpace ℝ (Fin m))
    (hbound : ∀ h : ℝ, h ≠ 0 → |h| < δ → ∃ W : GlobalC2Holder m α,
      globalC2Value W = (fun x => χ x * OAI.Analysis.PDE.Weak.differenceQuotient v h u x) ∧ ‖W‖ ≤ M)
    {K : Set (EuclideanSpace ℝ (Fin m))} (hK : IsCompact K) (hconv : Convex ℝ K) :
    ContDiffOn ℝ 2 (fun x => χ x * fderiv ℝ u x v) (interior K) ∧
      ∀ x ∈ interior K, ∀ y ∈ interior K,
        ‖fderiv ℝ (fderiv ℝ (fun z => χ z * fderiv ℝ u z v)) x -
          fderiv ℝ (fderiv ℝ (fun z => χ z * fderiv ℝ u z v)) y‖ ≤ M * (dist x y) ^ α := by
  classical
  let h : ℕ → ℝ := fun k => (δ / 2) * (1 / ((k : ℝ) + 1))
  have hpos (k) : 0 < h k := by dsimp only [h]; positivity
  have hne (k) : h k ≠ 0 := ne_of_gt (hpos k)
  have hsmall (k) : |h k| < δ := by
    rw [abs_of_pos (hpos k)]
    have hone : 1 / ((k : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).mpr
      simp only [one_mul]
      linarith only [Nat.cast_nonneg (α := ℝ) k]
    have hh := mul_le_mul_of_nonneg_left hone (show 0 ≤ δ / 2 by positivity)
    dsimp only [h]
    nlinarith only [hh, hδ]
  have ht : Tendsto h atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall (fun k => ?_)⟩
    · simpa only [mul_zero] using
        (tendsto_const_nhds (x := δ / 2)).mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · simpa only [mem_compl_iff, mem_singleton_iff] using hne k
  choose W hW hnorm using fun k => hbound (h k) (hne k) (hsmall k)
  apply globalC2Holder_pointwise_limit hα hK hconv W hnorm
  intro x _
  have hp := (tendsto_differenceQuotient u v x (hu x)).comp ht
  simpa only [hW, Function.comp_def] using tendsto_const_nhds.mul hp

theorem contDiff_directional_derivative_of_local_schauder_bound {m : ℕ} {α M δ : ℝ}
    (hα : 0 < α) (hδ : 0 < δ)
    (u χ : EuclideanSpace ℝ (Fin m) → ℝ) (hu : Differentiable ℝ u)
    (v : EuclideanSpace ℝ (Fin m))
    (hbound : ∀ h : ℝ, h ≠ 0 → |h| < δ → ∃ W : GlobalC2Holder m α,
      globalC2Value W = (fun x => χ x * OAI.Analysis.PDE.Weak.differenceQuotient v h u x) ∧ ‖W‖ ≤ M) :
    ContDiff ℝ 2 (fun x => χ x * fderiv ℝ u x v) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hx : x ∈ interior (closedBall x 1) := mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds x zero_lt_one)
  have hc := (directional_derivative_C2_of_local_schauder_bound hα hδ u χ hu v hbound
    (isCompact_closedBall x 1) (convex_closedBall x 1)).1
  exact (hc x hx).contDiffAt (isOpen_interior.mem_nhds hx)

end OAI.Analysis.PDE.Schauder
