import OAI.RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits

/-! # Restricted Integral Neighborhoods -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RestrictedIntegralNeighborhoods.CM

noncomputable section

/-! ThetaCycle: inside the product of the actual local integral subgroups,
a restricted-product neighborhood imposes conditions at only finitely
many places, in the original local group topologies. -/

open Filter
open scoped Classical RestrictedProduct _root_.Topology

theorem restricted_integral_neighborhood {I : Type*} {G : I → Type*}
    [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
    (K : ∀ i, Subgroup (G i))
    (U : Set (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K))
    (hU : U ∈ 𝓝 (1 : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K)) :
    ∃ (J : Finset I) (V : ∀ i, Set (G i)), (∀ i, V i ∈ 𝓝 (1 : G i)) ∧
      ∀ g : RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K,
        (∀ i, g i ∈ K i) → (∀ i ∈ J, g i ∈ V i) → g ∈ U := by
  let f : (∀ i, K i) → RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup K :=
    RestrictedProduct.structureMap G (fun i => (K i : Set (G i))) cofinite
  have hf : Continuous f := RestrictedProduct.isEmbedding_structureMap.continuous
  have hone : f 1 = 1 := rfl
  have hpre : f ⁻¹' U ∈ 𝓝 (1 : ∀ i, K i) := hf.continuousAt.preimage_mem_nhds (hone.symm ▸ hU)
  rw [nhds_pi] at hpre
  obtain ⟨J, W, hW, hsub⟩ := mem_pi'.mp hpre
  have he (i : I) : ∃ V : Set (G i), V ∈ 𝓝 (1 : G i) ∧
      (fun x : K i => (x : G i)) ⁻¹' V ⊆ W i := by
    have h := hW i
    rw [nhds_subtype_eq_comap] at h
    exact mem_comap.mp h
  choose V hV hVW using he
  refine ⟨J, V, hV, ?_⟩
  intro g hg hJ
  let x : ∀ i, K i := fun i => ⟨g i, hg i⟩
  have hx : x ∈ Set.pi (J : Set I) W := by
    intro i hi
    exact hVW i (hJ i hi)
  have hfg : f x = g := by
    apply RestrictedProduct.ext
    intro i
    rfl
  have hh : f x ∈ U := hsub hx
  exact hfg ▸ hh

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RestrictedIntegralNeighborhoods.CM
