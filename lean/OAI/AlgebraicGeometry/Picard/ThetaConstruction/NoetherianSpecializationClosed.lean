import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sober

/-! # Noetherian Specialization Closed -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.NoetherianSpecializationClosed.Geometric

/-! In a Noetherian sober space, an open set stable under
specialization is a finite union of irreducible components. -/

open Set _root_.TopologicalSpace

theorem isClosed_of_isOpen_stableUnderSpecialization
    {X : Type*} [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X]
    {s : Set X} (hs : IsOpen s) (hst : StableUnderSpecialization s) : IsClosed s := by
  let C := {Z ∈ irreducibleComponents X | Z ⊆ s}
  have hC : C.Finite := NoetherianSpace.finite_irreducibleComponents.subset (fun _ h => h.1)
  have he : s = ⋃ Z ∈ C, Z := by
    apply Set.Subset.antisymm
    · intro x hx
      let Z := irreducibleComponent x
      have hZ := irreducibleComponent_mem_irreducibleComponents x
      have hclosed := isClosed_of_mem_irreducibleComponents Z hZ
      have hη := hZ.1.isGenericPoint_genericPoint hclosed
      have hxZ : x ∈ Z := mem_irreducibleComponent
      have hηs := hs.stableUnderGeneralization (hη.specializes hxZ) hx
      have hsub : Z ⊆ s := fun y hy => hst (hη.specializes hy) hηs
      exact Set.mem_iUnion.mpr ⟨Z, Set.mem_iUnion.mpr ⟨⟨hZ, hsub⟩, hxZ⟩⟩
    · intro x hx
      obtain ⟨Z, hZ, hxZ⟩ := Set.mem_iUnion₂.mp hx
      exact hZ.2 hxZ
  rw [he]
  exact hC.isClosed_biUnion (fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1)

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.NoetherianSpecializationClosed.Geometric
