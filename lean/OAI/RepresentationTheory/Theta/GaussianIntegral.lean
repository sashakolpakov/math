import OAI.RepresentationTheory.Theta.PoissonAutomorphyGaussianPoisson

/-! # Gaussian Integral -/

namespace OAI.RepresentationTheory.Theta.GaussianIntegral.PoissonAutomorphyConstruction

noncomputable section

section

/-! Linear changes of variables in the real coordinate space. -/

open scoped Classical _root_.Matrix
open _root_.Matrix _root_.MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def realMatrixEquiv (L : Matrix ι ι ℝ) (hL : L.det ≠ 0) : (ι → ℝ) ≃L[ℝ] (ι → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { L.mulVecLin with
      invFun := fun x => L⁻¹ *ᵥ x
      left_inv := fun x => by
        change L⁻¹ *ᵥ (L *ᵥ x) = x
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul L (isUnit_iff_ne_zero.mpr hL),
          Matrix.one_mulVec]
      right_inv := fun x => by
        change L *ᵥ (L⁻¹ *ᵥ x) = x
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv L (isUnit_iff_ne_zero.mpr hL),
          Matrix.one_mulVec] }

theorem realMatrixEquiv_apply (L : Matrix ι ι ℝ) (hL : L.det ≠ 0) (x : ι → ℝ) :
    realMatrixEquiv L hL x = L *ᵥ x := rfl

theorem integral_comp_realMatrix (L : Matrix ι ι ℝ) (hL : L.det ≠ 0)
    (f : (ι → ℝ) → ℂ) :
    (∫ x, f (L *ᵥ x)) = ((|L.det|⁻¹ : ℝ) : ℂ) * ∫ x, f x := by
  have hmap : Measure.map (realMatrixEquiv L hL) volume =
      ENNReal.ofReal (|L.det|⁻¹) • volume := by
    change Measure.map L.mulVecLin volume = _
    simpa only [abs_inv, Matrix.toLin'_apply'] using
      Real.map_matrix_volume_pi_eq_smul_volume_pi hL
  have h := (realMatrixEquiv L hL).toHomeomorph.measurableEmbedding.integral_map (μ := volume) f
  change (∫ y, f y ∂Measure.map (realMatrixEquiv L hL) volume) = ∫ x, f (L *ᵥ x) at h
  rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg _))] at h
  simpa only [realMatrixEquiv_apply, Complex.real_smul] using h.symm

theorem integral_eq_det_mul_comp (L : Matrix ι ι ℝ) (hL : L.det ≠ 0)
    (f : (ι → ℝ) → ℂ) :
    (∫ x, f x) = ((|L.det| : ℝ) : ℂ) * ∫ x, f (L *ᵥ x) := by
  rw [integral_comp_realMatrix L hL, ← mul_assoc, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (abs_ne_zero.mpr hL), Complex.ofReal_one, one_mul]

def complexVector (x : ι → ℝ) : ι → ℂ := fun i => (x i : ℂ)

omit [DecidableEq ι] in
theorem complexVector_mulVec (L : Matrix ι ι ℝ) (x : ι → ℝ) :
    complexVector (L *ᵥ x) = L.map (algebraMap ℝ ℂ) *ᵥ complexVector x := by
  ext i
  simp [complexVector, Matrix.mulVec, dotProduct]

omit [DecidableEq ι] in
theorem gaussianExponent_matrix (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ)
    (x : ι → ℝ) :
    PoissonAutomorphyGaussianPoisson.Construction.gaussianExponent Z z x = (Real.pi : ℂ) * Complex.I *
      (complexVector x ⬝ᵥ (Z.matrix *ᵥ complexVector x)) +
      (2 * (Real.pi : ℂ) * Complex.I) * (complexVector x ⬝ᵥ z) := by
  simp only [PoissonAutomorphyGaussianPoisson.Construction.gaussianExponent, AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix.phase,
    AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm_apply, AlgebraicGeometry.ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing_apply,
    complexVector, dotProduct, Matrix.mulVec, Finset.mul_sum]
  simp only [mul_comm, mul_left_comm, mul_assoc]

end

/-! Evaluation of the Gaussian integral with a general Siegel matrix. -/

open scoped Classical _root_.Matrix
open _root_.Matrix _root_.MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def diagonalGaussianMass (d : ι → ℝ) : ℂ :=
  ∏ i, ((Real.pi : ℂ) / (-((Real.pi : ℂ) * Complex.I) * ((d i : ℂ) + Complex.I))) ^ (1 / 2 : ℂ)

theorem diagonal_siegel_entry_ne_zero (t : ℝ) : (t : ℂ) + Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  norm_num at this

theorem gaussian_integral_diagonalized (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι)
    (L : Matrix ι ι ℝ) (d : ι → ℝ) (hL : L.det ≠ 0)
    (hdiag : (L.map (algebraMap ℝ ℂ)).transpose * Z.matrix * L.map (algebraMap ℝ ℂ) =
      Matrix.diagonal (fun i => (d i : ℂ) + Complex.I)) (z : ι → ℂ) :
    (∫ x, PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction Z z x) =
      ((|L.det| : ℝ) : ℂ) * diagonalGaussianMass d *
        Complex.exp (-(Real.pi : ℂ) * Complex.I *
          ∑ i, ((L.map (algebraMap ℝ ℂ)).transpose *ᵥ z) i ^ 2 / ((d i : ℂ) + Complex.I)) := by
  let w := (L.map (algebraMap ℝ ℂ)).transpose *ᵥ z
  let b : ι → ℂ := fun i => -((Real.pi : ℂ) * Complex.I) * ((d i : ℂ) + Complex.I)
  let c : ι → ℂ := fun i => 2 * (Real.pi : ℂ) * Complex.I * w i
  have hb (i : ι) : 0 < (b i).re := by
    simpa [b, Complex.mul_re, Complex.mul_im] using Real.pi_pos
  have hexp (x : ι → ℝ) : PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction Z z (L *ᵥ x) =
      Complex.exp (-∑ i, b i * (x i : ℂ) ^ 2 + ∑ i, c i * (x i : ℂ)) := by
    unfold PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction
    rw [gaussianExponent_matrix, complexVector_mulVec, AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM.bilinear_matrix_pullback, hdiag]
    have hlin : (L.map (algebraMap ℝ ℂ) *ᵥ complexVector x) ⬝ᵥ z = complexVector x ⬝ᵥ w := by
      exact (dotProduct_comm _ _).trans
        (Matrix.dotProduct_transpose_mulVec (L.map (algebraMap ℝ ℂ)) (complexVector x) z).symm
    rw [hlin]
    congr 1
    simp only [dotProduct, Matrix.mulVec_diagonal, complexVector, Finset.mul_sum, b, c,
      ← Finset.sum_neg_distrib]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
  have hscalar (i : ι) : c i ^ 2 / (4 * b i) =
      -(Real.pi : ℂ) * Complex.I * (w i ^ 2 / ((d i : ℂ) + Complex.I)) := by
    dsimp [b, c]
    field_simp [diagonal_siegel_entry_ne_zero (d i), Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    ring
  rw [integral_eq_det_mul_comp L hL]
  simp_rw [hexp]
  rw [GaussianFourier.integral_cexp_neg_sum_mul_add hb c, Finset.prod_mul_distrib, ← Complex.exp_sum]
  simp_rw [hscalar]
  rw [← Finset.mul_sum]
  simp only [diagonalGaussianMass, b, w, mul_assoc]

theorem inverse_of_congruence_diagonal (Z L : Matrix ι ι ℂ) (d : ι → ℂ)
    (hL : L.det ≠ 0) (hd : ∀ i, d i ≠ 0) (hdiag : L.transpose * Z * L = Matrix.diagonal d) :
    Z⁻¹ = L * Matrix.diagonal (fun i => (d i)⁻¹) * L.transpose := by
  have h := congrArg (fun M : Matrix ι ι ℂ => L * M⁻¹ * L.transpose) hdiag
  have hdi : (Matrix.diagonal d)⁻¹ = Matrix.diagonal (fun i => (d i)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    simp only [mul_inv_cancel₀ (hd _), Matrix.diagonal_one]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hdi] at h
  have hLt : IsUnit L.transpose.det := by simpa using isUnit_iff_ne_zero.mpr hL
  simpa only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv L (isUnit_iff_ne_zero.mpr hL),
    one_mul, Matrix.nonsing_inv_mul_cancel_right _ _ hLt] using h

def gaussianMass (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) : ℂ := ∫ x, PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction Z 0 x

theorem gaussian_integral (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (z : ι → ℂ) :
    (∫ x, PoissonAutomorphyGaussianPoisson.Construction.gaussianFunction Z z x) = gaussianMass Z *
      Complex.exp (-(Real.pi : ℂ) * Complex.I * (z ⬝ᵥ (Z.matrix⁻¹ *ᵥ z))) := by
  obtain ⟨L, d, hL, hdiag⟩ := PoissonAutomorphyGaussianPoisson.Construction.siegel_real_diagonalization Z
  have hLc : (L.map (algebraMap ℝ ℂ)).det ≠ 0 := by
    change ((algebraMap ℝ ℂ).mapMatrix L).det ≠ 0
    rw [← RingHom.map_det]
    exact Complex.ofReal_ne_zero.mpr hL
  have hinv := inverse_of_congruence_diagonal Z.matrix (L.map (algebraMap ℝ ℂ))
    (fun i => (d i : ℂ) + Complex.I) hLc (fun i => diagonal_siegel_entry_ne_zero (d i)) hdiag
  have hmass : gaussianMass Z = ((|L.det| : ℝ) : ℂ) * diagonalGaussianMass d := by
    rw [gaussianMass, gaussian_integral_diagonalized Z L d hL hdiag]
    simp
  rw [hmass, gaussian_integral_diagonalized Z L d hL hdiag, hinv]
  congr 2
  have hpull := AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM.bilinear_matrix_pullback (L.map (algebraMap ℝ ℂ)).transpose
    (Matrix.diagonal (fun i => ((d i : ℂ) + Complex.I)⁻¹)) z
  simp only [Matrix.transpose_transpose] at hpull
  rw [← hpull]
  simp [Matrix.mulVec_diagonal, dotProduct, div_eq_mul_inv, mul_comm, mul_left_comm, pow_two]

end

end OAI.RepresentationTheory.Theta.GaussianIntegral.PoissonAutomorphyConstruction
