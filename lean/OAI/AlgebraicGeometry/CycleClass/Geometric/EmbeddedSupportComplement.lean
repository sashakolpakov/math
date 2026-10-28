import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Sets.Opens

/-! # Embedded Support Complement -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.EmbeddedSupportComplement.Cycles

/-! # The actual open complement of a closed embedded support -/

open _root_.TopologicalSpace

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]

/-- The open complement of the full image of a genuine closed embedding. -/
def embeddedSupportComplement (f : M → N) (hf : Topology.IsClosedEmbedding f) : Opens N :=
  ⟨(Set.range f)ᶜ, hf.isClosed_range.isOpen_compl⟩

@[simp]
theorem mem_embeddedSupportComplement (f : M → N) (hf : Topology.IsClosedEmbedding f)
    (y : N) : y ∈ embeddedSupportComplement f hf ↔ y ∉ Set.range f := Iff.rfl

end OAI.AlgebraicGeometry.CycleClass.Geometric.EmbeddedSupportComplement.Cycles
