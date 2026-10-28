import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Local

/-! # Dual Scalar Lattices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.DualScalarLattices

noncomputable section

/-! Scaling a lattice by a unit inversely scales its bilinear dual. -/

open scoped Pointwise

variable {R K V : Type*} [CommRing R] [Field K] [Algebra R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

theorem dualSubmodule_unit_smul (B : LinearMap.BilinForm K V) (L : Submodule R V) (a : Kˣ) :
    B.dualSubmodule (a • L) = a⁻¹ • B.dualSubmodule L := by
  ext x
  change (∀ y ∈ a • (L : Set V), B x y ∈ (1 : Submodule R K)) ↔
    x ∈ a⁻¹ • (B.dualSubmodule L : Set V)
  rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
  constructor
  · intro hx y hy
    have h := hx (a • y) ⟨y, hy, rfl⟩
    change B ((a : K) • x) y ∈ (1 : Submodule R K)
    simpa only [Units.smul_def, map_smul, LinearMap.smul_apply, smul_eq_mul] using h
  · intro hx y hy
    obtain ⟨z, hz, rfl⟩ := hy
    have h := hx z hz
    change B x ((a : K) • z) ∈ (1 : Submodule R K)
    simpa only [Units.smul_def, map_smul, LinearMap.smul_apply, smul_eq_mul] using h

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.DualScalarLattices
