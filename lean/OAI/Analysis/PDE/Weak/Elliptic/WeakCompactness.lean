import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.InnerProductSpace.Dual

/-! Weak compactness in a real Hilbert space, retaining every scalar limit.
This will be applied to bounded difference quotients in the actual L² space. -/

noncomputable section
open Set Filter InnerProductSpace
open scoped Topology
namespace OAI.Analysis.PDE.Weak

theorem exists_weak_limit_preserving_scalar_limits {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (u : ℕ → H) {C : ℝ} (hC : ∀ n, ‖u n‖ ≤ C) :
    ∃ g : H, ‖g‖ ≤ C ∧ ∀ (v : H) (l : ℝ),
      Tendsto (fun n ↦ inner ℝ (u n) v) atTop (𝓝 l) → inner ℝ g v = l := by
  let w : ℕ → WeakDual ℝ H := fun n ↦ StrongDual.toWeakDual (toDual ℝ H (u n))
  let K : Set (WeakDual ℝ H) := WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 C
  have hc : IsCompact K := WeakDual.isCompact_closedBall 0 C
  have hmem : Tendsto w atTop (𝓟 K) := by
    apply tendsto_principal.mpr
    apply Eventually.of_forall
    intro n
    change toDual ℝ H (u n) ∈ Metric.closedBall 0 C
    simpa using hC n
  obtain ⟨z, hz, hcluster⟩ := hc.exists_clusterPt hmem
  let g : H := (toDual ℝ H).symm (WeakDual.toStrongDual z)
  refine ⟨g, ?_, ?_⟩
  · change WeakDual.toStrongDual z ∈ Metric.closedBall 0 C at hz
    simpa [g] using hz
  · intro v l hl
    have hlim : Tendsto (fun a : WeakDual ℝ H ↦ a v) (map w atTop) (𝓝 l) := by
      change Tendsto (fun n ↦ inner ℝ (u n) v) atTop (𝓝 l)
      exact hl
    have hc' := hcluster.map (WeakDual.eval_continuous v).continuousAt hlim
    have he : z v = l := eq_of_nhds_neBot hc'
    change (toDual ℝ H g) v = l
    simpa [g] using he

end OAI.Analysis.PDE.Weak
