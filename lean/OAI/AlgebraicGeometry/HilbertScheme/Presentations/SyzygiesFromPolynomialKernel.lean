import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Linear.PolynomialCoefficients

/-! # Syzygies From Polynomial Kernel -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.SyzygiesFromPolynomialKernel.GradedHilbert

noncomputable section

/-! Generators of the polynomial substitution kernel give actual generators of the relation module. -/

open _root_.MvPolynomial

variable {R ι : Type*} [CommRing R] [Fintype ι]

def polynomialRelationMap (g : ι → R) : (ι → R) →ₗ[R] R where
  toFun a := ∑ i, a i * g i
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' r a := by simp [mul_assoc, Finset.mul_sum]

def polynomialLinearForm (a : ι → R) : MvPolynomial ι R :=
  ∑ i, C (a i) * X i

theorem polynomialLinearPart_linearForm (a : ι → R) :
    Linear.PolynomialCoefficients.GradedHilbert.polynomialLinearPart (polynomialLinearForm a) = a := by
  classical
  funext j
  simp [polynomialLinearForm, map_sum, Linear.PolynomialCoefficients.GradedHilbert.polynomialLinearPart_mul, Linear.PolynomialCoefficients.GradedHilbert.polynomialLinearPart_C,
    Linear.PolynomialCoefficients.GradedHilbert.polynomialLinearPart_X, Finset.sum_apply, Pi.single_apply]

theorem linearVariableSubstitution_linearForm (g a : ι → R) :
    Linear.PolynomialCoefficients.GradedHilbert.linearVariableSubstitution g (polynomialLinearForm a) =
      Polynomial.C (polynomialRelationMap g a) * Polynomial.X := by
  have hC (r : R) : Linear.PolynomialCoefficients.GradedHilbert.linearVariableSubstitution g (C r) = Polynomial.C r := by
    simp [Linear.PolynomialCoefficients.GradedHilbert.linearVariableSubstitution]
  have hX (i : ι) : Linear.PolynomialCoefficients.GradedHilbert.linearVariableSubstitution g (X i) = Polynomial.C (g i) * Polynomial.X := by
    simp [Linear.PolynomialCoefficients.GradedHilbert.linearVariableSubstitution]
  simp only [polynomialLinearForm, map_sum, map_mul, hC, hX, ← mul_assoc]
  simp only [← map_mul]
  rw [← Finset.sum_mul, ← map_sum]
  rfl

theorem syzygy_kernel_eq_span_linearParts (g : ι → R) (B : Set (MvPolynomial ι R))
    (hB : RingHom.ker (Linear.PolynomialCoefficients.GradedHilbert.linearVariableSubstitution g).toRingHom = Ideal.span B) :
    LinearMap.ker (polynomialRelationMap g) = Submodule.span R (Linear.PolynomialCoefficients.GradedHilbert.polynomialLinearPart '' B) := by
  have hzero (b : MvPolynomial ι R) (hb : b ∈ B) : Linear.PolynomialCoefficients.GradedHilbert.linearVariableSubstitution g b = 0 := by
    apply RingHom.mem_ker.mp
    change b ∈ RingHom.ker (Linear.PolynomialCoefficients.GradedHilbert.linearVariableSubstitution g).toRingHom
    rw [hB]
    exact Ideal.subset_span hb
  have hconstant (b : MvPolynomial ι R) (hb : b ∈ B) : constantCoeff b = 0 := by
    rw [← Linear.PolynomialCoefficients.GradedHilbert.linearVariableSubstitution_coeff_zero g, hzero b hb, Polynomial.coeff_zero]
  apply le_antisymm
  · intro a ha
    have hp : polynomialLinearForm a ∈ Ideal.span B := by
      rw [← hB, RingHom.mem_ker]
      change Linear.PolynomialCoefficients.GradedHilbert.linearVariableSubstitution g (polynomialLinearForm a) = 0
      rw [linearVariableSubstitution_linearForm, LinearMap.mem_ker.mp ha, map_zero, zero_mul]
    have h := (Linear.PolynomialCoefficients.GradedHilbert.polynomialLinearPart_mem_span B hconstant hp).2
    rwa [polynomialLinearPart_linearForm] at h
  · apply Submodule.span_le.mpr
    rintro a ⟨b, hb, rfl⟩
    change polynomialRelationMap g (Linear.PolynomialCoefficients.GradedHilbert.polynomialLinearPart b) = 0
    change (∑ i, Linear.PolynomialCoefficients.GradedHilbert.polynomialLinearPart b i * g i) = 0
    rw [← Linear.PolynomialCoefficients.GradedHilbert.linearVariableSubstitution_coeff_one, hzero b hb, Polynomial.coeff_zero]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.SyzygiesFromPolynomialKernel.GradedHilbert
