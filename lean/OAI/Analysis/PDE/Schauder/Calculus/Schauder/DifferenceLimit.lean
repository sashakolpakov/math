import OAI.Analysis.PDE.Schauder.Calculus.Schauder.DifferenceCalculus
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.CompactLimit

/-! Uniform Schauder bounds identify an actual C² directional derivative. -/

noncomputable section
open Set Filter Metric
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Weak

theorem directional_derivative_C2_of_schauder_bound {m : ℕ} {α M : ℝ} (hα : 0 < α)
    (u χ : EuclideanSpace ℝ (Fin m) → ℝ) (hu : Differentiable ℝ u)
    (v : EuclideanSpace ℝ (Fin m))
    (hbound : ∀ h : ℝ, h ≠ 0 → ∃ W : GlobalC2Holder m α,
      globalC2Value W = (fun x => χ x * OAI.Analysis.PDE.Weak.differenceQuotient v h u x) ∧ ‖W‖ ≤ M)
    {K : Set (EuclideanSpace ℝ (Fin m))} (hK : IsCompact K) (hconv : Convex ℝ K) :
    ContDiffOn ℝ 2 (fun x => χ x * fderiv ℝ u x v) (interior K) ∧
      ∀ x ∈ interior K, ∀ y ∈ interior K,
        ‖fderiv ℝ (fderiv ℝ (fun z => χ z * fderiv ℝ u z v)) x -
          fderiv ℝ (fderiv ℝ (fun z => χ z * fderiv ℝ u z v)) y‖ ≤ M * (dist x y) ^ α := by
  classical
  let h : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hpos (k) : 0 < h k := by dsimp only [h]; positivity
  have hne (k) : h k ≠ 0 := ne_of_gt (hpos k)
  have ht : Tendsto h atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall (fun k => ?_)⟩
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
    · simpa only [mem_compl_iff, mem_singleton_iff] using hne k
  choose W hW hnorm using fun k => hbound (h k) (hne k)
  apply globalC2Holder_pointwise_limit hα hK hconv W hnorm
  intro x _
  have hp := (tendsto_differenceQuotient u v x (hu x)).comp ht
  simpa only [hW, Function.comp_def] using tendsto_const_nhds.mul hp

theorem contDiff_directional_derivative_of_schauder_bound {m : ℕ} {α M : ℝ} (hα : 0 < α)
    (u χ : EuclideanSpace ℝ (Fin m) → ℝ) (hu : Differentiable ℝ u)
    (v : EuclideanSpace ℝ (Fin m))
    (hbound : ∀ h : ℝ, h ≠ 0 → ∃ W : GlobalC2Holder m α,
      globalC2Value W = (fun x => χ x * OAI.Analysis.PDE.Weak.differenceQuotient v h u x) ∧ ‖W‖ ≤ M) :
    ContDiff ℝ 2 (fun x => χ x * fderiv ℝ u x v) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hx : x ∈ interior (closedBall x 1) := mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds x zero_lt_one)
  have hc := (directional_derivative_C2_of_schauder_bound hα u χ hu v hbound
    (isCompact_closedBall x 1) (convex_closedBall x 1)).1
  exact (hc x hx).contDiffAt (isOpen_interior.mem_nhds hx)

end OAI.Analysis.PDE.Schauder
