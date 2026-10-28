import OAI.NumberTheory.ArithmeticGroups.Lattices.RelativeSubgroupProductCoordinates
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-! # Subgroup Relative Equiv -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.SubgroupRelativeEquiv.Construction

noncomputable section

/-! A subgroup contained in an ambient subgroup is continuously
isomorphic to its relative presentation inside that subgroup. -/

def subgroupRelativeEquiv
    {G : Type*} [Group G] [TopologicalSpace G]
    (H P : Subgroup G) (hP : P ≤ H) : P ≃ₜ* P.comap H.subtype where
  toFun p := ⟨⟨p.val, hP p.property⟩, p.property⟩
  invFun p := ⟨p.val.val, p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.SubgroupRelativeEquiv.Construction
