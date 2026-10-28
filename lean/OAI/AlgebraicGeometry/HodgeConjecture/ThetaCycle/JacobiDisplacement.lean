import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealGaussianCoefficient

/-! # Jacobi Displacement -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.JacobiDisplacement.CM

noncomputable section

section

/-! ThetaCycle: the Jacobi Gaussian is a concrete Heisenberg displacement of
the Gaussian at zero, with its exact exponential scalar. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

theorem gaussian_exponent_matrix {N : ℕ} (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N))
    (z : Fin N → ℂ) (x : Fin N → ℝ) :
    RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianExponent Z z x = (Real.pi : ℂ) * Complex.I *
      ((fun i => (x i : ℂ)) ⬝ᵥ (Z.matrix *ᵥ fun i => (x i : ℂ))) +
      (2 * (Real.pi : ℂ) * Complex.I) * ((fun i => (x i : ℂ)) ⬝ᵥ z) := by
  simp only [RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianExponent, ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix.phase, ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm_apply,
    ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing_apply, dotProduct, Matrix.mulVec, Finset.mul_sum,
    mul_assoc, mul_comm, mul_left_comm]

theorem complex_gaussian_displacement {I : Type*} [Fintype I]
    (Z : Matrix I I ℂ) (hZ : Z.IsSymm) (x q p : I → ℂ) :
    (Real.pi : ℂ) * Complex.I * ((x - q) ⬝ᵥ (Z *ᵥ (x - q))) +
        (2 * (Real.pi : ℂ) * Complex.I) * (p ⬝ᵥ (x - (1 / 2 : ℂ) • q)) =
      -((Real.pi : ℂ) * Complex.I * (q ⬝ᵥ (p - Z *ᵥ q))) +
        ((Real.pi : ℂ) * Complex.I * (x ⬝ᵥ (Z *ᵥ x)) +
          (2 * (Real.pi : ℂ) * Complex.I) * (x ⬝ᵥ (p - Z *ᵥ q))) := by
  have hcross : q ⬝ᵥ (Z *ᵥ x) = x ⬝ᵥ (Z *ᵥ q) := by
    simpa only [hZ.eq] using Matrix.dotProduct_transpose_mulVec Z q x
  simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, dotProduct_smul, hcross]
  rw [dotProduct_comm p x, dotProduct_comm p q]
  ring

def displacementJacobi {N : ℕ} (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (q p : Fin N → ℝ) : Fin N → ℂ :=
  (fun i => (p i : ℂ)) - Z.matrix *ᵥ (fun i => (q i : ℂ))

def displacementScalar {N : ℕ} (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (q p : Fin N → ℝ) : ℂ :=
  Complex.exp (-((Real.pi : ℂ) * Complex.I *
    ((fun i => (q i : ℂ)) ⬝ᵥ displacementJacobi Z q p)))

theorem displacement_scalar_ne_zero {N : ℕ} (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (q p : Fin N → ℝ) :
    displacementScalar Z q p ≠ 0 := Complex.exp_ne_zero _

theorem heisenberg_gaussian_displacement {N : ℕ} (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N))
    (q p x : Fin N → ℝ) :
    RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction (RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter 1) (Sum.elim q p) (RealGaussianCoefficient.CM.realSiegelGaussian Z 0).val x =
      displacementScalar Z q p * (RealGaussianCoefficient.CM.realSiegelGaussian Z (displacementJacobi Z q p)).val x := by
  simp only [RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction, Sum.elim_inl, Sum.elim_inr, RepresentationTheory.Weil.Local.Gaussian.Construction.realCharacter_apply,
    RealGaussianCoefficient.CM.real_siegel_gaussian_apply, RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction, displacementScalar]
  rw [← Complex.exp_add, ← Complex.exp_add, gaussian_exponent_matrix, gaussian_exponent_matrix]
  have hxq : (fun i => ((x i - q i : ℝ) : ℂ)) =
      (fun i => (x i : ℂ)) - (fun i => (q i : ℂ)) := by ext i; simp
  have hchar : (((2 * Real.pi * 1 * (∑ i, p i * (x i - q i / 2)) : ℝ) : ℂ) * Complex.I) =
      (2 * (Real.pi : ℂ) * Complex.I) *
        ((fun i => (p i : ℂ)) ⬝ᵥ ((fun i => (x i : ℂ)) - (1 / 2 : ℂ) • (fun i => (q i : ℂ)))) := by
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_sum, Complex.ofReal_sub, Complex.ofReal_inv, dotProduct, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, one_mul,
      mul_assoc, mul_comm, mul_left_comm]
  congr 1
  rw [hchar, hxq]
  simp only [dotProduct_zero, mul_zero, add_zero]
  rw [add_comm]
  exact complex_gaussian_displacement Z.matrix Z.symmetric _ _ _

end

/-! ThetaCycle: every complex Jacobi parameter is represented by an actual
real position and momentum displacement, using the positive imaginary part. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

theorem displacement_jacobi_re {N : ℕ} (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N))
    (q p : Fin N → ℝ) (i : Fin N) :
    (displacementJacobi Z q p i).re = p i - ((Z.matrix.map Complex.re) *ᵥ q) i := by
  simp only [displacementJacobi, Pi.sub_apply, Complex.sub_re, Complex.ofReal_re,
    Matrix.mulVec, dotProduct, Complex.re_sum, Complex.mul_re, Complex.ofReal_im,
    mul_zero, sub_zero, Matrix.map_apply]

theorem displacement_jacobi_im {N : ℕ} (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N))
    (q p : Fin N → ℝ) (i : Fin N) :
    (displacementJacobi Z q p i).im = -((Z.matrix.map Complex.im) *ᵥ q) i := by
  simp only [displacementJacobi, Pi.sub_apply, Complex.sub_im, Complex.ofReal_im,
    Matrix.mulVec, dotProduct, Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
    mul_zero, zero_add, zero_sub, Matrix.map_apply]

def jacobiPositionShift {N : ℕ} (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (z : Fin N → ℂ) : Fin N → ℝ :=
  -((Z.matrix.map Complex.im)⁻¹ *ᵥ (fun i => (z i).im))

def jacobiMomentumShift {N : ℕ} (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (z : Fin N → ℂ) : Fin N → ℝ :=
  (fun i => (z i).re) + (Z.matrix.map Complex.re) *ᵥ jacobiPositionShift Z z

theorem jacobi_position_shift_equation {N : ℕ} (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (z : Fin N → ℂ) :
    (Z.matrix.map Complex.im) *ᵥ jacobiPositionShift Z z = -(fun i => (z i).im) := by
  have hdet : IsUnit (Z.matrix.map Complex.im).det :=
    isUnit_iff_ne_zero.mpr Z.imaginary_posDef.det_pos.ne'
  rw [jacobiPositionShift, Matrix.mulVec_neg, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

theorem jacobi_displacement_coordinates {N : ℕ} (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (z : Fin N → ℂ) :
    displacementJacobi Z (jacobiPositionShift Z z) (jacobiMomentumShift Z z) = z := by
  funext i
  apply Complex.ext
  · rw [displacement_jacobi_re]
    change (z i).re + _ - _ = (z i).re
    exact add_sub_cancel_right _ _
  · rw [displacement_jacobi_im, jacobi_position_shift_equation]
    simp only [Pi.neg_apply, neg_neg]

theorem exists_real_jacobi_displacement {N : ℕ} (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (z : Fin N → ℂ) :
    ∃ q p : Fin N → ℝ, displacementJacobi Z q p = z :=
  ⟨jacobiPositionShift Z z, jacobiMomentumShift Z z, jacobi_displacement_coordinates Z z⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.JacobiDisplacement.CM
