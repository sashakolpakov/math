import Mathlib

/-! # Compact Reconstruction -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.CompactReconstruction

/-! A continuous reconstruction from observed coordinates transfers
compact bounds to a closed embedded space. -/

open Set _root_.Topology

theorem isCompact_preimage_of_reconstruction {X E V : Type*}
    [TopologicalSpace X] [TopologicalSpace E] [TopologicalSpace V] [T2Space V]
    (f : X → E) (hf : IsClosedEmbedding f) (g : X → V) (hg : Continuous g)
    (r : V → E) (hr : Continuous r) (hrec : ∀ x, r (g x) = f x)
    (C : Set V) (hC : IsCompact C) : IsCompact (g ⁻¹' C) := by
  apply (hf.isCompact_preimage (hC.image hr)).of_isClosed_subset (hC.isClosed.preimage hg)
  intro x hx
  exact ⟨g x, hx, hrec x⟩

end OAI.NumberTheory.Quaternion.Arithmetic.CompactReconstruction
