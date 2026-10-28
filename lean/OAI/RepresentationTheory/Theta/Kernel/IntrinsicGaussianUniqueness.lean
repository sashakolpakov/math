import OAI.RepresentationTheory.Theta.Kernel.Analysis
import OAI.RepresentationTheory.Weil.Local.RealGenerators
import OAI.RepresentationTheory.Weil.Local.FourierEquivalence

/-! # Intrinsic Gaussian Uniqueness -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Kernel.IntrinsicGaussianUniqueness.IntrinsicBounds

/-! A nearby positive Gaussian and its squared difference from the
reference Gaussian are dominated by the integrable reference Gaussian. -/

open _root_.MeasureTheory
open scoped Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

def phaseGaussian (B : V →L[ℝ] V →L[ℝ] ℂ) (x : V) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * B x x)

theorem nearby_half_imaginary (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase V) (B : V →L[ℝ] V →L[ℝ] ℂ)
    (hB : ‖B - Z.form‖ ≤ Z.lowerBound / 2) (x : V) :
    (Z.form x x).im / 2 ≤ (B x x).im := by
  have heval : ‖(B - Z.form) x x‖ ≤ (Z.lowerBound / 2) * ‖x‖ ^ 2 := by
    calc
      _ ≤ ‖(B - Z.form) x‖ * ‖x‖ := ((B - Z.form) x).le_opNorm x
      _ ≤ (‖B - Z.form‖ * ‖x‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right ((B - Z.form).le_opNorm x) (norm_nonneg x)
      _ ≤ ((Z.lowerBound / 2) * ‖x‖) * ‖x‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB (norm_nonneg x)) (norm_nonneg x)
      _ = _ := by ring
  have hi := (neg_le_abs ((B - Z.form) x x).im).trans ((Complex.abs_im_le_norm _).trans heval)
  simp only [sub_apply,Complex.sub_im] at hi
  have hZ := Z.imaginaryQuadratic_lower_bound x
  change Z.lowerBound * ‖x‖ ^ 2 ≤ (Z.form x x).im at hZ
  nlinarith

omit [FiniteDimensional ℝ V] in
theorem phase_gaussian_norm (B : V →L[ℝ] V →L[ℝ] ℂ) (x : V) :
    ‖phaseGaussian B x‖ = Real.exp (-Real.pi * (B x x).im) := by
  rw [phaseGaussian,Complex.norm_exp]
  congr 1
  simp [Complex.mul_re,Complex.mul_im]

omit [FiniteDimensional ℝ V] in
theorem positive_gaussian_norm_le_one (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase V) (x : V) :
    ‖phaseGaussian Z.form x‖ ≤ 1 := by
  rw [phase_gaussian_norm]
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le)
    (Z.imaginaryQuadratic_nonneg x)

theorem nearby_gaussian_square_bound (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase V) (B : V →L[ℝ] V →L[ℝ] ℂ)
    (hB : ‖B - Z.form‖ ≤ Z.lowerBound / 2) (x : V) :
    ‖phaseGaussian B x‖ ^ 2 ≤ ‖phaseGaussian Z.form x‖ := by
  rw [phase_gaussian_norm,phase_gaussian_norm,pow_two,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (nearby_half_imaginary Z B hB x) Real.pi_pos.le
  nlinarith

theorem nearby_gaussian_difference_bound (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelPhase.CM.SiegelPhase V) (B : V →L[ℝ] V →L[ℝ] ℂ)
    (hB : ‖B - Z.form‖ ≤ Z.lowerBound / 2) (x : V) :
    ‖phaseGaussian B x - phaseGaussian Z.form x‖ ^ 2 ≤ 4 * ‖phaseGaussian Z.form x‖ := by
  have hB' := nearby_gaussian_square_bound Z B hB x
  have hZ := positive_gaussian_norm_le_one Z x
  have ht := pow_le_pow_left₀ (norm_nonneg (phaseGaussian B x - phaseGaussian Z.form x))
    (norm_sub_le (phaseGaussian B x) (phaseGaussian Z.form x)) 2
  nlinarith [sq_nonneg (‖phaseGaussian B x‖ - ‖phaseGaussian Z.form x‖),
    mul_nonneg (norm_nonneg (phaseGaussian Z.form x)) (sub_nonneg.mpr hZ)]

theorem siegel_gaussian_phase {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) (x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n) :
    Weil.Local.SiegelGaussian.Construction.siegelGaussian Z x = phaseGaussian (AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm Z) x := by
  unfold Weil.Local.SiegelGaussian.Construction.siegelGaussian phaseGaussian
  congr 1
  congr 1
  simp only [AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm_apply,dotProduct,Matrix.mulVec,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem reference_gaussian_integrable {n : ℕ} (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin n)) :
    Integrable (fun x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n => ‖phaseGaussian Z.phase.form x‖)
      (Weil.Local.UnitaryInner.Construction.referencePositionMeasure ℝ n) := by
  have hg : Integrable (Weil.Local.SiegelGaussian.Construction.siegelGaussian Z.matrix) (Weil.Local.UnitaryInner.Construction.referencePositionMeasure ℝ n) := by
    rw [Measure.isAddLeftInvariant_eq_smul_of_regular (Weil.Local.UnitaryInner.Construction.referencePositionMeasure ℝ n) volume]
    exact (Weil.Local.SiegelGaussian.Construction.siegelGaussian_integrable Z.matrix Z.symmetric Z.imaginary_posDef).smul_measure (by simp)
  change Integrable (fun x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n => ‖phaseGaussian (AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm Z.matrix) x‖) _
  simpa only [siegel_gaussian_phase] using hg.norm

end RepresentationTheory.Theta.Kernel.IntrinsicGaussianUniqueness.IntrinsicBounds

namespace RepresentationTheory.Theta.Kernel.IntrinsicGaussianUniqueness.IntrinsicHeisenberg

/-! Jacobi-variable Gaussians as actual Heisenberg translates of the
positive zero-centred Gaussian, with the exact scalar exponent. -/

open scoped Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianUniqueness.IntrinsicBounds

def realJacobi {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) (q p : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n) : Fin n → ℂ :=
  fun i => (p i : ℂ) - Z.mulVec (fun j => (q j : ℂ)) i

def jacobiGaussian {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) (ξ : Fin n → ℂ)
    (x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm Z x x +
    (2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (x i : ℂ) * ξ i)

def shiftFactor {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) (q p : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I *
    (AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm Z q q - ((∑ i, q i * p i : ℝ) : ℂ)))

theorem real_jacobi_pairing {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ)
    (x q p : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n) :
    (∑ i, (x i : ℂ) * realJacobi Z q p i) =
      ((∑ i, x i * p i : ℝ) : ℂ) - AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm Z x q := by
  simp only [realJacobi,mul_sub,Finset.sum_sub_distrib,Complex.ofReal_sum,Complex.ofReal_mul]
  congr 1
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum,AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadratic_subtract {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℂ) (x q : V) :
    B (x - q) (x - q) = B x x - B x q - B q x + B q q := by
  simp only [map_sub,sub_apply]
  ring

theorem real_shift_pairing {n : ℕ} (x q p : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n) :
    (∑ i, p i * (x i - q i / 2)) = (∑ i, x i * p i) - (∑ i, q i * p i) / 2 := by
  calc
    _ = ∑ i, (x i * p i - (q i * p i) / 2) :=
      Finset.sum_congr rfl (fun _ _ => by ring)
    _ = _ := by rw [Finset.sum_sub_distrib,Finset.sum_div]

theorem heisenberg_gaussian_formula {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ)
    (hZ : Z.IsSymm) (q p x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n) :
    Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction (Weil.Local.Gaussian.Construction.realCharacter 1) (Sum.elim q p) (Weil.Local.SiegelGaussian.Construction.siegelGaussian Z) x =
      shiftFactor Z q p * jacobiGaussian Z (realJacobi Z q p) x := by
  have hq := quadratic_subtract (AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm Z) x q
  rw [AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm_symmetric Z hZ q x] at hq
  simp only [Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction,Sum.elim_inl,Sum.elim_inr,Weil.Local.Gaussian.Construction.realCharacter_apply,
    IntrinsicBounds.siegel_gaussian_phase,IntrinsicBounds.phaseGaussian,shiftFactor,jacobiGaussian]
  rw [real_shift_pairing,real_jacobi_pairing]
  change Complex.exp (↑(2 * Real.pi * 1 * ((∑ i, x i * p i) - (∑ i, q i * p i) / 2)) * Complex.I) *
    Complex.exp ((Real.pi : ℂ) * Complex.I * AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm Z (x - q) (x - q)) = _
  rw [hq,← Complex.exp_add,← Complex.exp_add]
  congr 1
  push_cast
  ring

def shiftedGaussianTest {n : ℕ} (φ : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (q p : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n) : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n :=
  ⟨Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction (Weil.Local.Gaussian.Construction.realCharacter 1) (Sum.elim q p) φ.val,Weil.Local.FourierEquivalence.Construction.real_heisenberg_mem 1 (Sum.elim q p) φ⟩

theorem shifted_gaussian_test_value {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ)
    (hZ : Z.IsSymm) (φ : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (hφ : φ.val = Weil.Local.SiegelGaussian.Construction.siegelGaussian Z)
    (q p : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n) (x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n) :
    (shiftedGaussianTest φ q p).val x = shiftFactor Z q p * jacobiGaussian Z (realJacobi Z q p) x := by
  change Weil.Local.FunctionsMetaplectic.Construction.heisenbergFunction (Weil.Local.Gaussian.Construction.realCharacter 1) (Sum.elim q p) φ.val x = _
  rw [hφ,heisenberg_gaussian_formula Z hZ]

end RepresentationTheory.Theta.Kernel.IntrinsicGaussianUniqueness.IntrinsicHeisenberg

namespace RepresentationTheory.Theta.Kernel.IntrinsicGaussianUniqueness.IntrinsicParameter

/-! An actual Jacobi Gaussian determines its parameter, even when its
value is specified only up to a constant scalar. This is used to recover
phase-space actions from actual Gaussian operator identities. -/

open scoped Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianUniqueness.IntrinsicHeisenberg

theorem exp_real_linear_injective (a b : ℂ)
    (h : ∀ t : ℝ, Complex.exp (a * t) = Complex.exp (b * t)) : a = b := by
  have hd (c : ℂ) : HasDerivAt (fun t : ℝ => Complex.exp (c * t)) c 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul c).cexp
  have he := funext h
  have ha := hd a
  rw [he] at ha
  exact ha.unique (hd b)

theorem jacobi_gaussian_parameter_unique {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ)
    (ξ η : Fin n → ℂ) (c : ℂ)
    (h : ∀ x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n, IntrinsicHeisenberg.jacobiGaussian Z ξ x = c * IntrinsicHeisenberg.jacobiGaussian Z η x) :
    c = 1 ∧ ξ = η := by
  have hc : c = 1 := by
    have hz := h 0
    simpa [IntrinsicHeisenberg.jacobiGaussian] using hz.symm
  refine ⟨hc,?_⟩
  have he (x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n) :
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (x i : ℂ) * ξ i) =
        Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (x i : ℂ) * η i) := by
    have hx := h x
    rw [hc,one_mul,IntrinsicHeisenberg.jacobiGaussian,IntrinsicHeisenberg.jacobiGaussian,Complex.exp_add,Complex.exp_add] at hx
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) hx
  funext j
  have hj := exp_real_linear_injective ((2 * (Real.pi : ℂ) * Complex.I) * ξ j)
    ((2 * (Real.pi : ℂ) * Complex.I) * η j) (by
      intro t
      have hcast : (fun i => ((Pi.single j t : Fin n → ℝ) i : ℂ)) = Pi.single j (t : ℂ) := by
        funext i
        by_cases hi : i = j <;> simp [hi]
      have hx := he (Pi.single j t)
      change Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
        ((fun i => ((Pi.single j t : Fin n → ℝ) i : ℂ)) ⬝ᵥ ξ)) =
          Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
            ((fun i => ((Pi.single j t : Fin n → ℝ) i : ℂ)) ⬝ᵥ η)) at hx
      rw [hcast,single_dotProduct,single_dotProduct] at hx
      simpa only [mul_assoc,mul_comm,mul_left_comm] using hx)
  exact mul_left_cancel₀ (mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) hj

theorem scaled_jacobi_parameter_unique {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ)
    (ξ η : Fin n → ℂ) (a b : ℂ) (ha : a ≠ 0)
    (h : ∀ x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ n, a * IntrinsicHeisenberg.jacobiGaussian Z ξ x = b * IntrinsicHeisenberg.jacobiGaussian Z η x) : ξ = η := by
  apply (jacobi_gaussian_parameter_unique Z ξ η (a⁻¹ * b) ?_).2
  intro x
  have hx := congrArg (fun c => a⁻¹ * c) (h x)
  simpa only [← mul_assoc,inv_mul_cancel₀ ha,one_mul] using hx

end RepresentationTheory.Theta.Kernel.IntrinsicGaussianUniqueness.IntrinsicParameter

namespace RepresentationTheory.Theta.Kernel.IntrinsicGaussianUniqueness.IntrinsicQuadratic

/-! A Gaussian exponential on a real vector space determines its
symmetric quadratic form. Real rescaling removes exponential periods. -/

open OAI.RepresentationTheory.Theta.Kernel.IntrinsicGaussianUniqueness.IntrinsicParameter

theorem exp_real_square_injective (a b : ℂ)
    (h : ∀ t : ℝ, Complex.exp (a * (t : ℂ) ^ 2) = Complex.exp (b * (t : ℂ) ^ 2)) : a = b := by
  have hpos (t : ℝ) (ht : 0 ≤ t) : Complex.exp (a * t) = Complex.exp (b * t) := by
    have hs : ((Real.sqrt t : ℝ) : ℂ) ^ 2 = (t : ℂ) := by exact_mod_cast Real.sq_sqrt ht
    have he := h (Real.sqrt t)
    rw [hs] at he
    exact he
  apply IntrinsicParameter.exp_real_linear_injective
  intro t
  by_cases ht : 0 ≤ t
  · exact hpos t ht
  · have he := hpos (-t) (by linarith)
    simp only [Complex.ofReal_neg,mul_neg,Complex.exp_neg] at he
    exact inv_injective he

theorem gaussian_bilinear_unique {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Q R : V →L[ℝ] V →L[ℝ] ℂ) (hQ : ∀ x y, Q x y = Q y x) (hR : ∀ x y, R x y = R y x)
    (h : ∀ x, Complex.exp (Q x x) = Complex.exp (R x x)) : Q = R := by
  have hdiag (x : V) : Q x x = R x x := by
    apply exp_real_square_injective
    intro t
    have hs (B : V →L[ℝ] V →L[ℝ] ℂ) : B (t • x) (t • x) = B x x * (t : ℂ) ^ 2 := by
      simp only [map_smul,_root_.smul_apply,Complex.real_smul]
      ring
    have he := h (t • x)
    rw [hs,hs] at he
    exact he
  ext x y
  have hxy := hdiag (x + y)
  simp only [map_add,_root_.add_apply,hQ y x,hR y x] at hxy
  have hc : (2 : ℂ) * Q x y = 2 * R x y := by
    linear_combination hxy - hdiag x - hdiag y
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) hc

end RepresentationTheory.Theta.Kernel.IntrinsicGaussianUniqueness.IntrinsicQuadratic

end

end OAI
