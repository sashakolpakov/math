import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.GroupTheory.IsPerfect

/-! # Dense Scalar Character -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DenseScalarCharacter.TestTransport

noncomputable section

/-! A scalar character on a dense subgroup of a perfect topological
group is trivial once it is trivial above an open identity subgroup.
No continuity of the scalar character is assumed. -/

open scoped Classical commutatorElement

variable {Γ G A : Type*} [Group Γ] [Group G] [CommGroup A]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (f : Γ →* G) (hf : DenseRange f) (χ : Γ →* A)

include hf in
theorem dense_character_kernel_commutators (x y : G) :
    ⁅x, y⁆ ∈ (χ.ker.map f).topologicalClosure := by
  have hc : Continuous (fun z : G × G => ⁅z.1, z.2⁆) := by
    simp only [commutatorElement_def]
    fun_prop
  have hs : IsClosed {z : G × G | ⁅z.1, z.2⁆ ∈ (χ.ker.map f).topologicalClosure} :=
    (χ.ker.map f).isClosed_topologicalClosure.preimage hc
  have hr : Set.range (Prod.map f f) ⊆ {z : G × G | ⁅z.1, z.2⁆ ∈ (χ.ker.map f).topologicalClosure} := by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    apply (χ.ker.map f).le_topologicalClosure
    refine ⟨⁅a, b⁆, ?_, map_commutatorElement f a b⟩
    change χ ⁅a, b⁆ = 1
    simp only [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
  exact closure_minimal hr hs ((hf.prodMap hf) (x, y))

include hf in
theorem dense_scalar_character_trivial
    (hperfect : commutator G = ⊤) (U : OpenSubgroup G)
    (hU : ∀ γ, f γ ∈ U → χ γ = 1) : ∀ γ, χ γ = 1 := by
  have htop : (χ.ker.map f).topologicalClosure = ⊤ := by
    apply top_unique
    rw [← hperfect]
    exact Subgroup.commutator_le.mpr (fun x _ y _ => dense_character_kernel_commutators f hf χ x y)
  intro γ
  have ho : IsOpen {x : G | x⁻¹ * f γ ∈ U} :=
    U.isOpen.preimage (continuous_inv.mul continuous_const)
  have hm : f γ ∈ closure (χ.ker.map f : Set G) := by
    change f γ ∈ (χ.ker.map f).topologicalClosure
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨x, hx, hxN⟩ := mem_closure_iff.mp hm _ ho (by simp)
  obtain ⟨δ, hδ, rfl⟩ := hxN
  change (f δ)⁻¹ * f γ ∈ U at hx
  have hdiff := hU (δ⁻¹ * γ) (by simpa only [map_mul, map_inv] using hx)
  change χ δ = 1 at hδ
  simpa only [map_mul, map_inv, hδ, inv_one, one_mul] using hdiff

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.DenseScalarCharacter.TestTransport
