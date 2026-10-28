import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeReflectionCongruence
import Mathlib.Data.Nat.ModEq

/-! # Cleared Lattice Isogenies -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ClearedLatticeIsogenies

noncomputable section

/-! The cleared rational reflection and its inverse give actual
integer-linear endomorphisms of the original lattice. Their composites
are multiplication by the square denominator, and each retains the
prescribed principal marking. -/

variable {E : Type*} [Field E]
    (Λ : Submodule ℤ (Fin 3 → E))
    (g : (Fin 3 → E) ≃ₗ[E] (Fin 3 → E)) (D : ℕ)

def clearedLatticeMap (h : ∀ x ∈ Λ, D • g x ∈ Λ) : Λ →ₗ[ℤ] Λ where
  toFun x := ⟨D • g x, h x x.property⟩
  map_add' x y := Subtype.ext (by
    change D • g ((x : Fin 3 → E) + y) = D • g x + D • g y
    rw [map_add, nsmul_add])
  map_smul' c x := Subtype.ext (by
    change D • g (c • (x : Fin 3 → E)) = c • (D • g x)
    rw [map_zsmul]
    exact smul_comm D c (g x))

theorem clearedLatticeMap_coe (h : ∀ x ∈ Λ, D • g x ∈ Λ) (x : Λ) :
    (clearedLatticeMap Λ g D h x : Fin 3 → E) = D • g x := rfl

theorem clearedLatticeMap_comp_inverse
    (h : ∀ x ∈ Λ, D • g x ∈ Λ) (hi : ∀ x ∈ Λ, D • g.symm x ∈ Λ) :
    (clearedLatticeMap Λ g D h).comp (clearedLatticeMap Λ g.symm D hi) =
      (D ^ 2 : ℤ) • (LinearMap.id : Λ →ₗ[ℤ] Λ) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change D • g (D • g.symm (x : Fin 3 → E)) = (D ^ 2 : ℤ) • (x : Fin 3 → E)
  rw [map_nsmul, LinearEquiv.apply_symm_apply, smul_smul]
  rw [← Nat.cast_pow, natCast_zsmul, pow_two]

theorem clearedLatticeMap_inverse_comp
    (h : ∀ x ∈ Λ, D • g x ∈ Λ) (hi : ∀ x ∈ Λ, D • g.symm x ∈ Λ) :
    (clearedLatticeMap Λ g.symm D hi).comp (clearedLatticeMap Λ g D h) =
      (D ^ 2 : ℤ) • (LinearMap.id : Λ →ₗ[ℤ] Λ) :=
  clearedLatticeMap_comp_inverse Λ g.symm D hi h

theorem clearedLatticeMap_principal
    {N : ℕ} (h : ∀ x ∈ Λ, D • g x ∈ Λ)
    (hc : ∀ x ∈ Λ, ∃ y ∈ Λ, D • g x - x = N • y) :
    ∀ x : Λ, ∃ y : Λ, clearedLatticeMap Λ g D h x - x = N • y := by
  intro x
  obtain ⟨y, hy, hxy⟩ := hc x x.property
  exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩

theorem exists_paired_principal_lattice_maps {N : ℕ}
    (hc : LatticeReflectionCongruence.ClearedPrincipalLatticeCongruence Λ N g) :
    ∃ (D : ℕ) (q v : Λ →ₗ[ℤ] Λ),
      0 < D ∧ Nat.Coprime D N ∧ Nat.ModEq N (D ^ 2) 1 ∧
      (∀ x : Λ, (q x : Fin 3 → E) = D • g x) ∧
      (∀ x : Λ, (v x : Fin 3 → E) = D • g.symm x) ∧
      q.comp v = (D ^ 2 : ℤ) • (LinearMap.id : Λ →ₗ[ℤ] Λ) ∧
      v.comp q = (D ^ 2 : ℤ) • (LinearMap.id : Λ →ₗ[ℤ] Λ) ∧
      (∀ x : Λ, ∃ y : Λ, q x - x = N • y) ∧
      (∀ x : Λ, ∃ y : Λ, v x - x = N • y) := by
  obtain ⟨D, hD, hcop, hmod, hf, hi⟩ := hc
  have hpres : ∀ x ∈ Λ, D • g x ∈ Λ := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hf x hx
    have hm : D • g x - x ∈ Λ := hxy.symm ▸ nsmul_mem hy N
    simpa only [sub_add_cancel] using Λ.add_mem hm hx
  have hipres : ∀ x ∈ Λ, D • g.symm x ∈ Λ := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hi x hx
    have hm : D • g.symm x - x ∈ Λ := hxy.symm ▸ nsmul_mem hy N
    simpa only [sub_add_cancel] using Λ.add_mem hm hx
  have hDmod : Nat.ModEq N D 1 :=
    (Nat.modEq_iff_dvd.mpr (by simpa only [Nat.cast_one] using hmod)).symm
  have hDsq : Nat.ModEq N (D ^ 2) 1 := by
    simpa only [one_pow] using hDmod.pow 2
  exact ⟨D, clearedLatticeMap Λ g D hpres, clearedLatticeMap Λ g.symm D hipres,
    hD, hcop, hDsq, fun _ => rfl, fun _ => rfl,
    clearedLatticeMap_comp_inverse Λ g D hpres hipres,
    clearedLatticeMap_inverse_comp Λ g D hpres hipres,
    clearedLatticeMap_principal Λ g D hpres hf,
    clearedLatticeMap_principal Λ g.symm D hipres hi⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ClearedLatticeIsogenies
