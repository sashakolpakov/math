import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicAwayRationals
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LatticeCoordinates
import OAI.RepresentationTheory.Theta.Geometric.AwayLattice

/-! # Away Lattice Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AwayLatticeCoordinates.TestTransport

noncomputable section

/-! The original lattice with q inverted is characterized in the same
integral basis by integrality at every other rational prime. -/

open scoped Classical

open _root_.Module

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]
  [Fintype J] (L : Submodule ℤ V) [Submodule.IsLattice ℚ L] (b : Basis J ℤ L)
  (q : ℕ) [Fact q.Prime]

omit [Fact q.Prime] in
theorem awayLattice_integer_coordinates (x : V) :
    x ∈ Submodule.span ℤ {y | ∃ n : ℕ, (q : ℤ) ^ n • y ∈ L} ↔
      ∀ j, ∃ n : ℕ, ∃ z : ℤ, (z : ℚ) = (q : ℚ) ^ n * (b.extendOfIsLattice ℚ).equivFun x j := by
  constructor
  · intro hx j
    obtain ⟨n, hn⟩ := (RepresentationTheory.Theta.Geometric.AwayLattice.mem_power_localized_lattice q L x).mp hx
    obtain ⟨z, hz⟩ := (LatticeCoordinates.TestTransport.lattice_mem_iff_integer_coordinates L b _).mp hn j
    refine ⟨n, z, ?_⟩
    simpa only [map_zsmul, Pi.smul_apply, zsmul_eq_mul, Int.cast_pow, Int.cast_natCast] using hz
  · intro hx
    have hs (j : J) : (b.extendOfIsLattice ℚ).equivFun x j • (b j).val ∈
        Submodule.span ℤ {y | ∃ n : ℕ, (q : ℤ) ^ n • y ∈ L} := by
      obtain ⟨n, z, hz⟩ := hx j
      apply Submodule.subset_span
      refine ⟨n, ?_⟩
      rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, Int.cast_pow, Int.cast_natCast, ← hz,
        Int.cast_smul_eq_zsmul]
      exact L.smul_mem z (b j).property
    have hsum := Submodule.sum_mem (t := Finset.univ) (Submodule.span ℤ {y | ∃ n : ℕ, (q : ℤ) ^ n • y ∈ L})
      (fun j _ => hs j)
    have he : (∑ j, (b.extendOfIsLattice ℚ).equivFun x j • (b j).val) = x := by
      simpa only [Basis.extendOfIsLattice_apply] using (b.extendOfIsLattice ℚ).sum_equivFun x
    exact he ▸ hsum

theorem awayLattice_padic_coordinates (x : V) :
    x ∈ Submodule.span ℤ {y | ∃ n : ℕ, (q : ℤ) ^ n • y ∈ L} ↔
      ∀ j, ∀ (p : ℕ) [Fact p.Prime], p ≠ q →
        ‖((b.extendOfIsLattice ℚ).equivFun x j : Padic p)‖ ≤ 1 := by
  rw [awayLattice_integer_coordinates L b q x]
  exact forall_congr' (fun j => (PadicAwayRationals.TestTransport.rational_integral_away_iff q _).symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AwayLatticeCoordinates.TestTransport
