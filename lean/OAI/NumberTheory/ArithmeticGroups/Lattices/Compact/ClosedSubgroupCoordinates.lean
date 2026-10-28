import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Group

/-! # Closed Subgroup Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.ClosedSubgroupCoordinates.Construction

noncomputable section

/-! A compact subgroup and a closed complementary subgroup give
global topological product coordinates whenever their product covers the group. -/

open Set

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def subgroupProductShear (K : Subgroup G) : K × G ≃ₜ K × G where
  toFun x := (x.1, x.1.val * x.2)
  invFun x := (x.1, x.1.val⁻¹ * x.2)
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem compact_closed_subgroup_product_isProperMap
    (K P : Subgroup G) (hK : IsCompact (K : Set G)) (hP : IsClosed (P : Set G)) :
    IsProperMap (fun x : K × P => x.1.val * x.2.val) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hinc : IsProperMap (Prod.map (id : K → K) (Subtype.val : P → G)) :=
    isProperMap_id.prodMap hP.isClosedEmbedding_subtypeVal.isProperMap
  have hshear := (subgroupProductShear K).isProperMap.comp hinc
  exact isProperMap_snd_of_compactSpace.comp hshear

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem disjoint_subgroup_product_injective
    (K P : Subgroup G) (hKP : K ⊓ P = ⊥) :
    Function.Injective (fun x : K × P => x.1.val * x.2.val) := by
  intro x y hxy
  change x.1.val * x.2.val = y.1.val * y.2.val at hxy
  have he : y.1.val⁻¹ * x.1.val = y.2.val * x.2.val⁻¹ := by
    calc
      y.1.val⁻¹ * x.1.val = y.1.val⁻¹ * (x.1.val * x.2.val) * x.2.val⁻¹ := by group
      _ = y.1.val⁻¹ * (y.1.val * y.2.val) * x.2.val⁻¹ := by rw [hxy]
      _ = y.2.val * x.2.val⁻¹ := by group
  have hm : y.1.val⁻¹ * x.1.val ∈ K ⊓ P :=
    ⟨K.mul_mem (K.inv_mem y.1.property) x.1.property,
      he.symm ▸ P.mul_mem y.2.property (P.inv_mem x.2.property)⟩
  rw [hKP] at hm
  have hk : x.1.val = y.1.val := (inv_mul_eq_one.mp hm).symm
  apply Prod.ext
  · exact Subtype.ext hk
  · apply Subtype.ext
    apply mul_left_cancel (a := y.1.val)
    simpa only [hk] using hxy

theorem compact_closed_subgroup_product_isHomeomorph
    (K P : Subgroup G) (hK : IsCompact (K : Set G)) (hP : IsClosed (P : Set G))
    (hKP : K ⊓ P = ⊥)
    (hcover : ∀ g : G, ∃ k : K, ∃ p : P, k.val * p.val = g) :
    IsHomeomorph (fun x : K × P => x.1.val * x.2.val) := by
  have hp := compact_closed_subgroup_product_isProperMap K P hK hP
  apply isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
  refine ⟨hp.continuous, hp.isClosedMap, disjoint_subgroup_product_injective K P hKP, ?_⟩
  intro g
  obtain ⟨k, p, h⟩ := hcover g
  exact ⟨(k, p), h⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.ClosedSubgroupCoordinates.Construction
