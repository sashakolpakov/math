import OAI.NumberTheory.ArithmeticGroups.Lattices.LatticeComparison
import OAI.NumberTheory.ArithmeticGroups.Lattices.StabilizerRestriction

/-! # Lattice Stabilizers -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.LatticeStabilizers.Construction

noncomputable section

/-! Commensurability of stabilizers for full integral lattices. -/

open scoped Classical Pointwise nonZeroDivisors _root_.NumberField

theorem stabilizer_relIndex_ne_zero_of_denominators
    {R V H : Type*} [CommRing R] [IsDomain R] [Ring.HasFiniteQuotients R]
    [AddCommGroup V] [Module R V] [Module.IsTorsionFree R V] [Group H]
    (ρ : H →* (V ≃ₗ[R] V)) (Λ Ω : Submodule R V) [Module.Finite R Λ]
    (d : R) (hd : d ≠ 0) (hΛΩ : d • Λ ≤ Ω) (hΩΛ : d • Ω ≤ Λ) :
    (SubmoduleOrbit.Construction.submoduleImageStabilizer ρ Ω).relIndex (SubmoduleOrbit.Construction.submoduleImageStabilizer ρ Λ) ≠ 0 := by
  let L : Submodule R Λ := (d • Ω).comap Λ.subtype
  have hL : (d ^ 2) • (⊤ : Submodule R Λ) ≤ L := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x (d ^ 2) ⊤).mp hx
    change (d ^ 2) • y.val ∈ d • Ω
    rw [pow_two, mul_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _
      (hΛΩ (Submodule.smul_mem_pointwise_smul _ _ _ y.property))
  have hindex := SubmoduleOrbit.Construction.submoduleImageStabilizer_finiteIndex (StabilizerRestriction.Construction.stabilizerRestriction ρ Λ) L
    (d ^ 2) (pow_ne_zero _ hd) hL
  have hsubgroup : SubmoduleOrbit.Construction.submoduleImageStabilizer (StabilizerRestriction.Construction.stabilizerRestriction ρ Λ) L =
      (SubmoduleOrbit.Construction.submoduleImageStabilizer ρ Ω).subgroupOf (SubmoduleOrbit.Construction.submoduleImageStabilizer ρ Λ) := by
    ext g
    change L.map (StabilizerRestriction.Construction.stabilizerRestriction ρ Λ g).toLinearMap = L ↔
      Ω.map (ρ g.val).toLinearMap = Ω
    exact (StabilizerRestriction.Construction.restriction_stabilizes_iff ρ Λ (d • Ω) hΩΛ g).trans
      (StabilizerRestriction.Construction.stabilizes_scalar_submodule_iff (ρ g.val) Ω d (smul_right_injective V hd))
  rw [hsubgroup] at hindex
  exact hindex.index_ne_zero

def restrictScalarsAutomorphismHom
    {R k V : Type*} [CommRing R] [Field k] [Algebra R k]
    [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower R k V] :
    (V ≃ₗ[k] V) →* (V ≃ₗ[R] V) where
  toFun := LinearEquiv.restrictScalars R
  map_one' := by ext x; rfl
  map_mul' _ _ := by ext x; rfl

theorem linearLatticeStabilizer_eq_imageStabilizer
    {k V H : Type*} [Field k] [NumberField k]
    [AddCommGroup V] [Module k V] [Module (𝓞 k) V] [IsScalarTower (𝓞 k) k V] [Group H]
    (ρ : H →* (V ≃ₗ[k] V)) (Λ : Submodule (𝓞 k) V) :
    IntegralLattice.linearLatticeStabilizer ρ Λ =
      SubmoduleOrbit.Construction.submoduleImageStabilizer (restrictScalarsAutomorphismHom.comp ρ) Λ := by
  ext g
  rw [StabilizerRestriction.Construction.submoduleImageStabilizer_mem_iff]
  rfl

theorem fullLattice_stabilizers_commensurable
    {k H : Type} [Field k] [NumberField k] [Group H] {n : ℕ}
    (ρ : H →* ((Fin n → k) ≃ₗ[k] (Fin n → k))) (Λ Ω : IntegralLattice.FullLattice k n) :
    (IntegralLattice.linearLatticeStabilizer ρ Λ.module).Commensurable
      (IntegralLattice.linearLatticeStabilizer ρ Ω.module) := by
  let : Module.Finite (𝓞 k) Λ.module := Module.Finite.iff_fg.mpr Λ.finite
  let : Module.Finite (𝓞 k) Ω.module := Module.Finite.iff_fg.mpr Ω.finite
  let : Ring.HasFiniteQuotients (𝓞 k) := Ring.HasFiniteQuotients.of_module_finite ℤ (𝓞 k)
  obtain ⟨d, hΛΩ, hΩΛ⟩ := LatticeComparison.Construction.fullLattices_commensurate_denominators Λ Ω
  have hd : (d : 𝓞 k) ≠ 0 := nonZeroDivisors.ne_zero d.property
  have hΛΩ' : (d : 𝓞 k) • Λ.module ≤ Ω.module := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists y (d : 𝓞 k) Λ.module).mp hy
    exact hΛΩ x hx
  have hΩΛ' : (d : 𝓞 k) • Ω.module ≤ Λ.module := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists y (d : 𝓞 k) Ω.module).mp hy
    exact hΩΛ x hx
  rw [linearLatticeStabilizer_eq_imageStabilizer, linearLatticeStabilizer_eq_imageStabilizer]
  exact ⟨⟨stabilizer_relIndex_ne_zero_of_denominators _ Ω.module Λ.module _ hd hΩΛ' hΛΩ'⟩,
    ⟨stabilizer_relIndex_ne_zero_of_denominators _ Λ.module Ω.module _ hd hΛΩ' hΩΛ'⟩⟩

theorem latticeStabilizer_commensurable_standard
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (Λ : IntegralLattice.FullLattice k n) :
    (G.latticeStabilizer Λ).Commensurable (G.latticeStabilizer (IntegralLattice.FullLattice.standard k n)) :=
  fullLattice_stabilizers_commensurable G.representation Λ (IntegralLattice.FullLattice.standard k n)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.LatticeStabilizers.Construction
