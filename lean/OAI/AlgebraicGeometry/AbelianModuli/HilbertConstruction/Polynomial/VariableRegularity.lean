import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Regular.IsSMulRegular

/-! # Variable Regularity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.VariableRegularity

noncomputable section

/-! A polynomial variable is regular after quotienting by any family of different variables. The proof uses the actual monomial support of the variable ideal, without a dimension hypothesis. -/
universe u v
variable {R : Type u} [CommRing R] {ι : Type v}

theorem fresh_variable_mul_mem_span_iff (S : Set ι) (j : ι) (hj : j ∉ S)
    (p : MvPolynomial ι R) :
    MvPolynomial.X j * p ∈ Ideal.span (MvPolynomial.X '' S) ↔
      p ∈ Ideal.span (MvPolynomial.X '' S) := by
  classical
  refine ⟨fun h => ?_, fun h => Ideal.mul_mem_left _ _ h⟩
  apply MvPolynomial.mem_ideal_span_X_image.mpr
  intro m hm
  have hshift : Finsupp.single j 1 + m ∈ (MvPolynomial.X j * p).support := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_X_mul]
    exact MvPolynomial.mem_support_iff.mp hm
  obtain ⟨i, hi, hmi⟩ := MvPolynomial.mem_ideal_span_X_image.mp h _ hshift
  have hij : j ≠ i := by
    intro heq
    exact hj (heq.symm ▸ hi)
  refine ⟨i, hi, ?_⟩
  simpa only [Finsupp.add_apply, Finsupp.single_eq_of_ne' hij, zero_add] using hmi

theorem fresh_variable_smul_regular_quotient (S : Set ι) (j : ι) (hj : j ∉ S) :
    IsSMulRegular (MvPolynomial ι R ⧸ Ideal.span ((MvPolynomial.X : ι → MvPolynomial ι R) '' S))
      (MvPolynomial.X j : MvPolynomial ι R) := by
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  intro z hz
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply (fresh_variable_mul_mem_span_iff S j hj p).mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  exact hz

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.VariableRegularity
