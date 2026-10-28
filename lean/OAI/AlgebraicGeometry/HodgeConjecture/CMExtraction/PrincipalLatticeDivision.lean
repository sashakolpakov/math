import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PrincipalLatticeGenerators
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LocalizedLatticeMaps

/-! # Principal Lattice Division -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PrincipalLatticeDivision.TestTransport

noncomputable section

/-! Congruence in a rational vector space is exact membership of the
divided difference in the original lattice. -/

open scoped Classical

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem lattice_multiple_iff_division (L : AddSubgroup V) (N : ℕ) (hN : 0 < N) (x : V) :
    (∃ y ∈ L, x = N • y) ↔ (N : ℚ)⁻¹ • x ∈ L := by
  have hN0 : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hN0, one_smul] using hy
  · intro hx
    refine ⟨(N : ℚ)⁻¹ • x, hx, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ hN0, one_smul]

theorem principalLattice_iff_division (L : Submodule ℤ V) (N : ℕ) (hN : 0 < N)
    (g : V ≃ₗ[ℚ] V) :
    g ∈ AbelianModuli.ReferenceFamily.Groups.principalLatticeSubgroup L.toAddSubgroup N ↔
      (∀ x ∈ L, g x ∈ L) ∧ (∀ x ∈ L, g.symm x ∈ L) ∧
        ∀ x ∈ L, (N : ℚ)⁻¹ • (g x - x) ∈ L := by
  change ((∀ x, x ∈ L ↔ g x ∈ L) ∧ ∀ x ∈ L, ∃ y ∈ L, g x - x = N • y) ↔ _
  constructor
  · rintro ⟨hg, hc⟩
    refine ⟨fun x hx => (hg x).mp hx, ?_, fun x hx =>
      (lattice_multiple_iff_division L.toAddSubgroup N hN _).mp (hc x hx)⟩
    intro x hx
    exact (hg (g.symm x)).mpr (by simpa only [LinearEquiv.apply_symm_apply] using hx)
  · rintro ⟨hg, hi, hc⟩
    refine ⟨fun x => ⟨hg x, fun hx => ?_⟩, fun x hx =>
      (lattice_multiple_iff_division L.toAddSubgroup N hN _).mpr (hc x hx)⟩
    simpa only [LinearEquiv.symm_apply_apply] using hi (g x) hx

theorem principalLattice_generators_division {A J : Type*} [CommRing A] [Module A V]
    (L : Submodule A V) (b : J → V) (hb : Submodule.span A (Set.range b) = L)
    (N : ℕ) (hN : 0 < N) (g : V ≃ₗ[A] V) :
    g ∈ AbelianModuli.ReferenceFamily.Groups.principalLatticeSubgroup L.toAddSubgroup N ↔
      (∀ j, g (b j) ∈ L) ∧ (∀ j, g.symm (b j) ∈ L) ∧
        ∀ j, (N : ℚ)⁻¹ • (g (b j) - b j) ∈ L := by
  rw [PrincipalLatticeGenerators.TestTransport.principalLattice_iff_generators L b hb N g]
  exact and_congr Iff.rfl (and_congr Iff.rfl
    (forall_congr' (fun j => lattice_multiple_iff_division L.toAddSubgroup N hN _)))

variable {J : Type*} [Fintype J] (L : Submodule ℤ V) (b : Module.Basis J ℤ L)

theorem principalPowerLocalizedLattice_iff_basis (q N : ℕ) (hN : 0 < N) (g : V ≃ₗ[ℚ] V) :
    g ∈ AbelianModuli.ReferenceFamily.Groups.principalLatticeSubgroup (LocalizedLatticeMaps.TestTransport.powerLocalizedLattice L q).toAddSubgroup N ↔
      (∀ j, g (b j).val ∈ LocalizedLatticeMaps.TestTransport.powerLocalizedLattice L q) ∧
      (∀ j, g.symm (b j).val ∈ LocalizedLatticeMaps.TestTransport.powerLocalizedLattice L q) ∧
      ∀ j, (N : ℚ)⁻¹ • (g (b j).val - (b j).val) ∈ LocalizedLatticeMaps.TestTransport.powerLocalizedLattice L q := by
  rw [principalLattice_iff_division _ N hN g]
  exact and_congr
    (LocalizedLatticeMaps.TestTransport.powerLocalizedLattice_map_iff_basis L q b (g.toLinearMap.restrictScalars ℤ))
    (and_congr (LocalizedLatticeMaps.TestTransport.powerLocalizedLattice_map_iff_basis L q b (g.symm.toLinearMap.restrictScalars ℤ))
      (LocalizedLatticeMaps.TestTransport.powerLocalizedLattice_map_iff_basis L q b
        (((N : ℚ)⁻¹ • (g.toLinearMap - LinearMap.id)).restrictScalars ℤ)))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PrincipalLatticeDivision.TestTransport
