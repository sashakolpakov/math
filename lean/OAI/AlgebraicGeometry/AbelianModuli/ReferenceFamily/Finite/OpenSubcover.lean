import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Sets.Opens

/-! # Open Subcover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.OpenSubcover

/-! A compact scheme space admits a finite subcover of its original
open cover, preserving every chosen affine chart and its frame. -/

open _root_.TopologicalSpace

theorem exists_finite_open_subcover {X I : Type*} [TopologicalSpace X] [CompactSpace X]
    (U : I → Opens X) (hU : iSup U = ⊤) :
    ∃ t : Finset I, iSup (fun i : t => U i.val) = ⊤ := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i => (U i : Set X)) (fun i => (U i).isOpen) (by
      intro x _
      have hx : x ∈ iSup U := by rw [hU]; trivial
      exact Set.mem_iUnion.mpr (Opens.mem_iSup.mp hx))
  refine ⟨t, top_unique ?_⟩
  intro x _
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ x))
  obtain ⟨hit, hx⟩ := Set.mem_iUnion.mp hi
  exact Opens.mem_iSup.mpr ⟨⟨i, hit⟩, hx⟩

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Finite.OpenSubcover
