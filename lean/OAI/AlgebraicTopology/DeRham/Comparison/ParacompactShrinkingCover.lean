import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.ShrinkingLemma
import Mathlib.Topology.Sets.Opens

/-! # Paracompact Shrinking Cover -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ParacompactShrinkingCover

noncomputable section

/-!
# Locally finite shrinking refinements of paracompact Hausdorff covers

The refinement is obtained from the actual paracompactness theorem and
mathlib's shrinking lemma. Its index set is the original cover's index set;
empty refined sets are allowed.
-/

open Set _root_.TopologicalSpace

variable {X ι : Type*} [TopologicalSpace X] [ParacompactSpace X] [T2Space X]

/-- Every open cover of a paracompact Hausdorff space has a locally finite
open refinement whose closures lie in the corresponding original sets. -/
theorem exists_locallyFinite_shrinking_cover (U : ι → Opens X) (hU : iSup U = ⊤) :
    ∃ V : ι → Opens X, iSup V = ⊤ ∧
      LocallyFinite (fun i => (V i : Set X)) ∧
      ∀ i, closure (V i : Set X) ⊆ (U i : Set X) := by
  have hcoverSet : (⋃ i, (U i : Set X)) = univ := by
    rw [← Opens.coe_iSup, hU, Opens.coe_top]
  obtain ⟨W, hWo, hWcover, hWfinite, hWU⟩ := precise_refinement
    (fun i => (U i : Set X)) (fun i => (U i).isOpen) hcoverSet
  obtain ⟨V, hVcover, hVo, hVW⟩ := exists_iUnion_eq_closure_subset
    hWo hWfinite.point_finite hWcover
  refine ⟨fun i => ⟨V i, hVo i⟩, ?_, ?_, ?_⟩
  · apply Opens.ext
    simpa only [Opens.coe_iSup, Opens.coe_top, Opens.coe_mk] using hVcover
  · exact hWfinite.subset fun i => subset_closure.trans (hVW i)
  · exact fun i => (hVW i).trans (hWU i)

end

end OAI.AlgebraicTopology.DeRham.Comparison.ParacompactShrinkingCover
