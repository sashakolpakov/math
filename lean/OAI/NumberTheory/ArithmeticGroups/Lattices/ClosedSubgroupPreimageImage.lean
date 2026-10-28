import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Algebra.Group.Subgroup.Map

/-! # Closed Subgroup Preimage Image -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ClosedSubgroupPreimageImage.Construction

/-! A closed homomorphism preimage inside a closed subgroup is closed
when viewed in the ambient group. -/

theorem closed_subgroup_preimage_image
    {G D : Type*} [Group G] [TopologicalSpace G] [Group D] [TopologicalSpace D]
    (F : Subgroup G) (hF : IsClosed (F : Set G)) (π : F →* D) (hπ : Continuous π)
    (A : Subgroup D) (hA : IsClosed (A : Set D)) :
    IsClosed ((A.comap π).map F.subtype : Set G) := by
  have hc : IsClosed (A.comap π : Set F) := hA.preimage hπ
  exact hF.isClosedMap_subtype_val _ hc

end OAI.NumberTheory.ArithmeticGroups.Lattices.ClosedSubgroupPreimageImage.Construction
