import OAI.Analysis.PDE.Concentration.LocalLaplacian
import Mathlib.Geometry.Manifold.PartitionOfUnity

namespace OAI.Analysis.PDE.Concentration

open Set Filter
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A local smooth function can be used in global calculus identities without
assuming a smooth extension: a cutoff constructs an extension agreeing on a
whole neighborhood of the chosen closed subset. -/
theorem exists_global_smooth_eq_near_closed {f : E → ℝ} {K U : Set E}
    (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U) (hf : ContDiffOn ℝ ∞ f U) :
    ∃ F : E → ℝ, ContDiff ℝ ∞ F ∧ ∀ x ∈ K, F =ᶠ[nhds x] f := by
  obtain ⟨W, hW, hKW, hWU⟩ := normal_exists_closure_subset hK hU hKU
  obtain ⟨V, hV, hKV, hVW⟩ := normal_exists_closure_subset hK hW hKW
  obtain ⟨β, hβ, _, hβsupp, hβone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hW isClosed_closure hVW
  have hβts : tsupport β ⊆ U := by simpa [tsupport, hβsupp] using hWU
  refine ⟨fun x => β x * f x, contDiff_iff_contDiffAt.mpr ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ tsupport β
    · exact hβ.contDiffAt.mul ((hf x (hβts hx)).contDiffAt (hU.mem_nhds (hβts hx)))
    · have he : (fun y => β y * f y) =ᶠ[nhds x] (fun _ => 0) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
        simp [hy]
      exact contDiffAt_const.congr_of_eventuallyEq he
  · intro x hx
    filter_upwards [hV.mem_nhds (hKV hx)] with y hy
    rw [(hβone y).mp (subset_closure hy), one_mul]

end OAI.Analysis.PDE.Concentration
