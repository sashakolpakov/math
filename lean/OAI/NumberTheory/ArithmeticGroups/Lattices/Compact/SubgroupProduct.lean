import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Connected.Clopen
import Mathlib.Algebra.Group.Subgroup.Basic

/-! # Subgroup Product -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.SubgroupProduct.Construction

/-! A compact subgroup times a closed subgroup is clopen when it
contains a neighborhood of the identity, and contains the identity component. -/

open scoped Pointwise _root_.Topology
open Set Filter

theorem subgroup_product_isOpen_of_mem_nhds
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K P : Subgroup G) (hnear : (K : Set G) * (P : Set G) ∈ 𝓝 (1 : G)) :
    IsOpen ((K : Set G) * (P : Set G)) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨k, hk, p, hp, rfl⟩
  let e := (Homeomorph.mulLeft k).trans (Homeomorph.mulRight p)
  have he : e '' ((K : Set G) * (P : Set G)) ∈ 𝓝 (k * p) := by
    have h : e '' ((K : Set G) * (P : Set G)) ∈ Filter.map e (𝓝 (1 : G)) := Filter.image_mem_map hnear
    rw [e.map_nhds_eq] at h
    have he1 : e 1 = k * p := by change k * 1 * p = k * p; rw [mul_one]
    simpa only [he1] using h
  apply Filter.mem_of_superset he
  rintro y ⟨z, ⟨u, hu, v, hv, rfl⟩, rfl⟩
  refine ⟨k * u, K.mul_mem hk hu, v * p, P.mul_mem hv hp, ?_⟩
  change (k * u) * (v * p) = (k * (u * v)) * p
  simp only [mul_assoc]

theorem compact_subgroup_product_isClopen
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K P : Subgroup G) (hK : IsCompact (K : Set G)) (hP : IsClosed (P : Set G))
    (hnear : (K : Set G) * (P : Set G) ∈ 𝓝 (1 : G)) :
    IsClopen ((K : Set G) * (P : Set G)) :=
  ⟨hP.mul_left_of_isCompact hK, subgroup_product_isOpen_of_mem_nhds K P hnear⟩

theorem connectedComponent_one_subset_compact_subgroup_product
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K P : Subgroup G) (hK : IsCompact (K : Set G)) (hP : IsClosed (P : Set G))
    (hnear : (K : Set G) * (P : Set G) ∈ 𝓝 (1 : G)) :
    connectedComponent (1 : G) ⊆ (K : Set G) * (P : Set G) := by
  apply isPreconnected_connectedComponent.subset_isClopen (compact_subgroup_product_isClopen K P hK hP hnear)
  exact ⟨1, mem_connectedComponent, ⟨1, K.one_mem, 1, P.one_mem, one_mul 1⟩⟩

end OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.SubgroupProduct.Construction
