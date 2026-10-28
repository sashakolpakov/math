import OAI.NumberTheory.ArithmeticGroups.Lattices.IntegralLattice

/-! # Lattice Comparison -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.LatticeComparison.Construction

noncomputable section

/-! Clearing denominators between full integral lattices. -/

open scoped Classical nonZeroDivisors _root_.NumberField
open OAI.NumberTheory.ArithmeticGroups.Lattices.IntegralLattice

section FractionModule
variable {R k V : Type*} [CommRing R] [Field k]
variable [Algebra R k] [IsFractionRing R k]
variable [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower R k V]

theorem denominator_of_full_submodule (Λ : Submodule R V)
    (hΛ : Submodule.span k (Λ : Set V) = ⊤) (x : V) :
    ∃ d : R⁰, (d : R) • x ∈ Λ := by
  let : IsLocalizedModule R⁰ (LinearMap.id : V →ₗ[R] V) := isLocalizedModule_id R⁰ V k
  have hx : x ∈ Λ.localized' k R⁰ (LinearMap.id : V →ₗ[R] V) := by
    rw [Submodule.localized'_eq_span]
    simpa only [LinearMap.id_coe, Set.image_id, hΛ] using (Submodule.mem_top (x := x))
  obtain ⟨m, hm, d, hd⟩ := (Submodule.mem_localized' _ _ _ _ _).mp hx
  refine ⟨d, ?_⟩
  have hmul := IsLocalizedModule.mk'_cancel' (LinearMap.id : V →ₗ[R] V) m d
  rw [hd] at hmul
  exact hmul ▸ hm

theorem full_submodule_isLocalized (Λ : Submodule R V)
    (hΛ : Submodule.span k (Λ : Set V) = ⊤) : IsLocalizedModule R⁰ Λ.subtype := by
  let hid : IsLocalizedModule R⁰ (LinearMap.id : V →ₗ[R] V) := isLocalizedModule_id R⁰ V k
  constructor
  · exact hid.map_units
  · intro x
    obtain ⟨d, hd⟩ := denominator_of_full_submodule Λ hΛ x
    exact ⟨(⟨(d : R) • x, hd⟩, d), rfl⟩
  · intro x y hxy
    exact ⟨1, by simpa using Subtype.val_injective hxy⟩

theorem common_denominator_for_fg (Λ Ω : Submodule R V) (hΛ : Λ.FG)
    (hΩ : Submodule.span k (Ω : Set V) = ⊤) :
    ∃ d : R⁰, ∀ x ∈ Λ, (d : R) • x ∈ Ω := by
  let : IsLocalizedModule R⁰ Ω.subtype := full_submodule_isLocalized Ω hΩ
  obtain ⟨S, hS⟩ := hΛ
  obtain ⟨d, hd⟩ := IsLocalizedModule.exist_integer_multiples_of_finset R⁰ Ω.subtype S
  refine ⟨d, fun x hx => ?_⟩
  rw [← hS] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨z, hz⟩ := hd y hy
      exact hz ▸ z.property
  | zero => simp
  | add y z _ _ hy hz => simpa only [smul_add] using Ω.add_mem hy hz
  | smul c y _ hy => simpa only [smul_comm (d : R) c y] using Ω.smul_mem c hy

end FractionModule

theorem fullLattices_commensurate_denominators
    {k : Type} [Field k] [NumberField k] {n : ℕ}
    (Λ Ω : IntegralLattice.FullLattice k n) :
    ∃ d : (𝓞 k)⁰,
      (∀ x ∈ Λ.module, (d : 𝓞 k) • x ∈ Ω.module) ∧
      (∀ x ∈ Ω.module, (d : 𝓞 k) • x ∈ Λ.module) := by
  obtain ⟨a, ha⟩ := common_denominator_for_fg Λ.module Ω.module Λ.finite Ω.full
  obtain ⟨b, hb⟩ := common_denominator_for_fg Ω.module Λ.module Ω.finite Λ.full
  refine ⟨a * b, ?_, ?_⟩
  · intro x hx
    simpa only [Submonoid.coe_mul, mul_smul, smul_comm (a : 𝓞 k) (b : 𝓞 k) x] using
      Ω.module.smul_mem (b : 𝓞 k) (ha x hx)
  · intro x hx
    simpa only [Submonoid.coe_mul, mul_smul] using Λ.module.smul_mem (a : 𝓞 k) (hb x hx)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.LatticeComparison.Construction
