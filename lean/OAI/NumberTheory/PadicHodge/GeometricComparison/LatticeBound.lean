import OAI.NumberTheory.PadicHodge.GeometricComparison.LatticeSubspaceEq
import OAI.NumberTheory.PadicHodge.GeometricComparison.SplitLattice

/-! # Lattice Bound -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.LatticeBound.LatticeHodgeBound

noncomputable section

/-! A full integral lattice with Frobenius divisibility bounds the dimension of the rational Hodge step. -/

open scoped nonZeroDivisors

theorem determinant_of_baseChange {R K M V : Type*} [CommRing R] [CommRing K]
    [Algebra R K] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (f : M →ₗ[R] V) (hf : IsBaseChange K f) (F : Module.End R M) (φ : Module.End K V)
    (hcomm : ∀ x, f (F x) = φ (f x)) :
    φ.det = algebraMap R K F.det := by
  have hφ : hf.endHom F = φ := by
    apply hf.algHom_ext
    intro x
    exact (hf.endHom_comp_apply F x).trans (hcomm x)
  rw [← hφ]
  exact hf.det_endHom K M F

theorem inequality (p : ℕ) [Fact p.Prime]
    {M V : Type*} [AddCommGroup M] [Module ℤ_[p] M]
    [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] M]
    [AddCommGroup V] [Module ℤ_[p] V] [Module ℚ_[p] V] [IsScalarTower ℤ_[p] ℚ_[p] V]
    (f : M →ₗ[ℤ_[p]] V) [IsLocalizedModule ℤ_[p]⁰ f]
    (F : Module.End ℤ_[p] M) (φ : Module.End ℚ_[p] V) (hφ : φ.det ≠ 0)
    (hcomm : ∀ x, f (F x) = φ (f x)) (H : Submodule ℚ_[p] V)
    (hdiv : ∀ x, f x ∈ H → ∃ y, F x = (p : ℤ_[p]) • y) :
    (Module.finrank ℚ_[p] H : ℤ) ≤ Padic.valuation φ.det := by
  let P := LatticeSubspaceEq.LatticeSubspace.integralPart f H
  let : Module.IsTorsionFree ℤ_[p] (M ⧸ P) := LatticeSubspaceEq.LatticeSubspace.quotient_torsionFree f H
  have hdet := determinant_of_baseChange f
    (IsLocalizedModule.isBaseChange ℤ_[p]⁰ ℚ_[p] f) F φ hcomm
  have hF : F.det ≠ 0 := by
    intro hz
    apply hφ
    rw [hdet, hz, map_zero]
  have hv := SplitLattice.SplitLatticeDeterminant.valuation_ge p P F hF (fun x => hdiv x x.property)
  rw [LatticeSubspaceEq.LatticeSubspace.finrank_eq f H] at hv
  change φ.det = (F.det : ℚ_[p]) at hdet
  rwa [← hdet] at hv

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.LatticeBound.LatticeHodgeBound
