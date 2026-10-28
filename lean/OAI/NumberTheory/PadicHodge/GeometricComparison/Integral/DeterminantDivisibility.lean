import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers

/-! # Determinant Divisibility -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.DeterminantDivisibility.IntegralDeterminantDivisibility

noncomputable section

/-! Divisibility of integral Frobenius columns supplies the determinant valuation bound used for a Hodge lattice. -/

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

theorem product_dvd_det (M : Matrix ι ι R) (d : ι → R)
    (h : ∀ i j, d j ∣ M i j) : (∏ j, d j) ∣ M.det := by
  choose N hN using h
  have hM : M = Matrix.of (fun i j => d j * N i j) := Matrix.ext hN
  erw [hM, Matrix.det_mul_row d (Matrix.of N)]
  exact dvd_mul_right _ _

theorem power_dvd_det (M : Matrix ι ι R) (p : R) (s : Finset ι)
    (h : ∀ j ∈ s, ∀ i, p ∣ M i j) : p ^ s.card ∣ M.det := by
  classical
  have hd : ∀ i j, (if j ∈ s then p else 1) ∣ M i j := by
    intro i j
    split_ifs with hj
    · exact h j hj i
    · exact one_dvd _
  simpa using product_dvd_det M (fun j => if j ∈ s then p else 1) hd

theorem padic_valuation_ge (p : ℕ) [Fact p.Prime] (M : Matrix ι ι ℤ_[p])
    (s : Finset ι) (hM : M.det ≠ 0) (h : ∀ j ∈ s, ∀ i, (p : ℤ_[p]) ∣ M i j) :
    (s.card : ℤ) ≤ Padic.valuation (M.det : ℚ_[p]) := by
  have hd := power_dvd_det M (p : ℤ_[p]) s h
  have hv : s.card ≤ M.det.valuation := by
    apply (PadicInt.mem_span_pow_iff_le_valuation M.det hM s.card).mp
    exact Ideal.mem_span_singleton.mpr hd
  rw [PadicInt.valuation_coe]
  exact_mod_cast hv

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.DeterminantDivisibility.IntegralDeterminantDivisibility
