import OAI.Analysis.Calculus.SmoothExtension.Periodic.Extension.Local

open Set Filter Metric
open scoped Topology ContDiff Manifold
noncomputable section
namespace OAI.Analysis.Calculus.SmoothExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_smooth_compact_one_on_compact {C : Set E} (hC : IsCompact C) :
    ∃ρ : E → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧
      (∀x, 0 ≤ ρ x) ∧ ∀x ∈ C, ρ x = 1 := by
  obtain ⟨R,hR,hCR⟩ := hC.isBounded.exists_pos_norm_le
  have hsub : C ⊆ interior (closedBall (0 : E) (R + 1)) := by
    intro x hx
    apply isOpen_ball.subset_interior_iff.mpr ball_subset_closedBall
    simp only [mem_ball,dist_zero_right]
    linarith [hCR x hx]
  obtain ⟨ρ,hρ1,hρ0,hρ⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ,E)) hC.isClosed hsub (n := (⊤ : ℕ∞))
  refine ⟨ρ,?_,?_,fun x ↦ (hρ x).1,fun x hx ↦ hρ1.self_of_nhdsSet x hx⟩
  · exact contMDiff_iff_contDiff.mp ρ.contMDiff
  · exact HasCompactSupport.intro (isCompact_closedBall (0 : E) (R + 1)) hρ0

end OAI.Analysis.Calculus.SmoothExtension
