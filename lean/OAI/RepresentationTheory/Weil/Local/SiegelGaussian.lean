import OAI.RepresentationTheory.Weil.Local.RealOscillator

/-! # Siegel Gaussian -/

namespace OAI.RepresentationTheory.Weil.Local.SiegelGaussian.Construction

noncomputable section

section

/-! Positive complex Lagrangian frames for the real Gaussian model. -/

open _root_.Matrix
open scoped ComplexOrder

def realSymplecticComplexMatrix {n : ℕ} (g : FunctionsMetaplectic.Construction.Symplectic ℝ n) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ := g.val.map Complex.ofRealHom

theorem realSymplecticComplexMatrix_symplectic {n : ℕ} (g : FunctionsMetaplectic.Construction.Symplectic ℝ n) :
    (realSymplecticComplexMatrix g)ᵀ * Matrix.J (Fin n) ℂ * realSymplecticComplexMatrix g = Matrix.J (Fin n) ℂ := by
  have h := SymplecticGroup.mem_iff.mp (SymplecticGroup.transpose_mem
    (SymplecticGroup.map_mem g.property Complex.ofRealHom))
  simpa only [realSymplecticComplexMatrix, transpose_transpose] using! h

theorem realSymplecticComplexMatrix_conjTranspose {n : ℕ} (g : FunctionsMetaplectic.Construction.Symplectic ℝ n) :
    (realSymplecticComplexMatrix g)ᴴ = (realSymplecticComplexMatrix g)ᵀ := by
  ext i j
  exact Complex.conj_ofReal _

theorem realSymplecticComplexMatrix_mul {n : ℕ} (g h : FunctionsMetaplectic.Construction.Symplectic ℝ n) :
    realSymplecticComplexMatrix (g * h) = realSymplecticComplexMatrix g * realSymplecticComplexMatrix h := by
  exact Matrix.map_mul

structure PositiveLagrangianFrame (n : ℕ) where
  matrix : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ
  isotropic : matrixᵀ * Matrix.J (Fin n) ℂ * matrix = 0
  positive : (Complex.I • (matrixᴴ * Matrix.J (Fin n) ℂ * matrix)).PosDef

@[ext] theorem PositiveLagrangianFrame.ext {n : ℕ} {P Q : PositiveLagrangianFrame n}
    (h : P.matrix = Q.matrix) : P = Q := by cases P; cases Q; cases h; rfl

def PositiveLagrangianFrame.act {n : ℕ} (g : FunctionsMetaplectic.Construction.Symplectic ℝ n) (P : PositiveLagrangianFrame n) :
    PositiveLagrangianFrame n where
  matrix := realSymplecticComplexMatrix g * P.matrix
  isotropic := by
    calc
      _ = P.matrixᵀ * ((realSymplecticComplexMatrix g)ᵀ * Matrix.J (Fin n) ℂ * realSymplecticComplexMatrix g) * P.matrix := by
        simp only [transpose_mul, Matrix.mul_assoc]
      _ = _ := by rw [realSymplecticComplexMatrix_symplectic, P.isotropic]
  positive := by
    have h : (realSymplecticComplexMatrix g * P.matrix)ᴴ * Matrix.J (Fin n) ℂ *
        (realSymplecticComplexMatrix g * P.matrix) = P.matrixᴴ * Matrix.J (Fin n) ℂ * P.matrix := by
      calc
        _ = P.matrixᴴ * ((realSymplecticComplexMatrix g)ᴴ * Matrix.J (Fin n) ℂ * realSymplecticComplexMatrix g) * P.matrix := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [realSymplecticComplexMatrix_conjTranspose, realSymplecticComplexMatrix_symplectic]
    rw [h]
    exact P.positive

theorem PositiveLagrangianFrame.act_one {n : ℕ} (P : PositiveLagrangianFrame n) : P.act 1 = P := by
  apply PositiveLagrangianFrame.ext
  change realSymplecticComplexMatrix 1 * P.matrix = P.matrix
  simp [realSymplecticComplexMatrix]

theorem PositiveLagrangianFrame.act_mul {n : ℕ} (g h : FunctionsMetaplectic.Construction.Symplectic ℝ n) (P : PositiveLagrangianFrame n) :
    P.act (g * h) = (P.act h).act g := by
  apply PositiveLagrangianFrame.ext
  change realSymplecticComplexMatrix (g * h) * P.matrix =
    realSymplecticComplexMatrix g * (realSymplecticComplexMatrix h * P.matrix)
  rw [realSymplecticComplexMatrix_mul, Matrix.mul_assoc]

def standardFrameMatrix (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n) ℂ :=
  fromRows (1 : Matrix (Fin n) (Fin n) ℂ) (Complex.I • 1)

def standardPositiveFrame (n : ℕ) : PositiveLagrangianFrame n where
  matrix := standardFrameMatrix n
  isotropic := by
    simp only [standardFrameMatrix, transpose_fromRows, transpose_one, transpose_smul, Matrix.J,
      Matrix.mul_assoc, fromBlocks_mul_fromRows, fromCols_mul_fromRows,
      zero_mul, neg_mul, one_mul, mul_one, zero_add, add_zero, neg_add_cancel]
  positive := by
    have h : Complex.I • ((standardFrameMatrix n)ᴴ * Matrix.J (Fin n) ℂ * standardFrameMatrix n) =
        (1 : Matrix (Fin n) (Fin n) ℂ) + 1 := by
      simp only [standardFrameMatrix, conjTranspose_fromRows_eq_fromCols_conjTranspose, conjTranspose_one,
        conjTranspose_smul, Matrix.J, Matrix.mul_assoc, fromBlocks_mul_fromRows,
        fromCols_mul_fromRows, zero_mul, neg_mul, one_mul, zero_add, add_zero, mul_one,
        Complex.star_def, Complex.conj_I, smul_add, smul_neg,
        smul_smul, Complex.I_mul_I, neg_one_smul, neg_neg, mul_neg, one_smul]
    rw [h]
    exact Matrix.PosDef.one.add Matrix.PosDef.one

end

section

/-! Coordinate matrices of positive Lagrangian frames are nonsingular. -/

open _root_.Matrix
open scoped ComplexOrder

def PositiveLagrangianFrame.position {n : ℕ} (P : PositiveLagrangianFrame n) : Matrix (Fin n) (Fin n) ℂ :=
  P.matrix.submatrix Sum.inl id

def PositiveLagrangianFrame.momentum {n : ℕ} (P : PositiveLagrangianFrame n) : Matrix (Fin n) (Fin n) ℂ :=
  P.matrix.submatrix Sum.inr id

theorem PositiveLagrangianFrame.fromRows {n : ℕ} (P : PositiveLagrangianFrame n) :
    Matrix.fromRows P.position P.momentum = P.matrix := by
  ext (i | i) j <;> rfl

theorem PositiveLagrangianFrame.coordinate_isotropic {n : ℕ} (P : PositiveLagrangianFrame n) :
    P.positionᵀ * P.momentum = P.momentumᵀ * P.position := by
  have h := P.isotropic
  rw [← P.fromRows] at h
  simp only [transpose_fromRows, Matrix.J, Matrix.mul_assoc, fromBlocks_mul_fromRows,
    fromCols_mul_fromRows, zero_mul, neg_mul, one_mul, zero_add, add_zero, mul_neg] at h
  exact neg_add_eq_zero.mp h

theorem PositiveLagrangianFrame.coordinate_positive {n : ℕ} (P : PositiveLagrangianFrame n) :
    (Complex.I • (-(P.positionᴴ * P.momentum) + P.momentumᴴ * P.position)).PosDef := by
  have h := P.positive
  rw [← P.fromRows] at h
  simpa only [conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.J, Matrix.mul_assoc,
    fromBlocks_mul_fromRows, fromCols_mul_fromRows, zero_mul, neg_mul, one_mul,
    zero_add, add_zero, mul_neg] using h

theorem PositiveLagrangianFrame.position_isUnit {n : ℕ} (P : PositiveLagrangianFrame n) :
    IsUnit P.position := by
  have hker (v : Fin n → ℂ) (hv : P.position *ᵥ v = 0) : v = 0 := by
    by_contra hzero
    have hpos := P.coordinate_positive.dotProduct_mulVec_pos hzero
    have hl : star v ⬝ᵥ ((P.positionᴴ * P.momentum) *ᵥ v) = 0 := by
      rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, hv]
      simp
    have hr : star v ⬝ᵥ ((P.momentumᴴ * P.position) *ᵥ v) = 0 := by
      rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, dotProduct_zero]
    have hp : star v ⬝ᵥ ((-(P.positionᴴ * P.momentum) + P.momentumᴴ * P.position) *ᵥ v) = 0 := by
      rw [Matrix.add_mulVec, Matrix.neg_mulVec, dotProduct_add, dotProduct_neg, hl, hr]
      simp
    rw [Matrix.smul_mulVec, dotProduct_smul, hp, smul_zero] at hpos
    exact (lt_irrefl (0 : ℂ)) hpos
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  apply sub_eq_zero.mp
  apply hker
  rw [Matrix.mulVec_sub, hxy, sub_self]

theorem PositiveLagrangianFrame.position_det_ne_zero {n : ℕ} (P : PositiveLagrangianFrame n) :
    P.position.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det P.position).mp P.position_isUnit).ne_zero

end

section

/-! Symmetric Gaussian matrices with positive imaginary part, obtained from frames. -/

open _root_.Matrix
open scoped ComplexOrder

def PositiveLagrangianFrame.quadraticMatrix {n : ℕ} (P : PositiveLagrangianFrame n) :
    Matrix (Fin n) (Fin n) ℂ := P.momentum * P.position⁻¹

theorem PositiveLagrangianFrame.position_mul_inv {n : ℕ} (P : PositiveLagrangianFrame n) :
    P.position * P.position⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr P.position_det_ne_zero)

theorem PositiveLagrangianFrame.quadraticMatrix_symmetric {n : ℕ} (P : PositiveLagrangianFrame n) :
    P.quadraticMatrix.IsSymm := by
  have hT : P.position⁻¹ᵀ * P.positionᵀ = 1 := by
    rw [← transpose_mul, P.position_mul_inv, transpose_one]
  change (P.momentum * P.position⁻¹)ᵀ = P.momentum * P.position⁻¹
  rw [transpose_mul]
  calc
    _ = P.position⁻¹ᵀ * (P.momentumᵀ * P.position) * P.position⁻¹ := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, P.position_mul_inv, mul_one]
    _ = P.position⁻¹ᵀ * (P.positionᵀ * P.momentum) * P.position⁻¹ := by rw [P.coordinate_isotropic]
    _ = _ := by rw [← Matrix.mul_assoc P.position⁻¹ᵀ P.positionᵀ, hT, one_mul]

theorem PositiveLagrangianFrame.quadraticMatrix_positive {n : ℕ} (P : PositiveLagrangianFrame n) :
    (Complex.I • (P.quadraticMatrixᴴ - P.quadraticMatrix)).PosDef := by
  have hInv : Function.Injective P.position⁻¹.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr (Matrix.isUnit_nonsing_inv_iff.mpr P.position_isUnit)
  have h := P.coordinate_positive.conjTranspose_mul_mul_same hInv
  have hH : P.position⁻¹ᴴ * P.positionᴴ = 1 := by
    rw [← conjTranspose_mul, P.position_mul_inv, conjTranspose_one]
  have hleft : P.position⁻¹ᴴ * (P.positionᴴ * P.momentum) * P.position⁻¹ = P.quadraticMatrix := by
    rw [← Matrix.mul_assoc P.position⁻¹ᴴ P.positionᴴ, hH, one_mul]
    rfl
  have hright : P.position⁻¹ᴴ * (P.momentumᴴ * P.position) * P.position⁻¹ = P.quadraticMatrixᴴ := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, P.position_mul_inv, mul_one]
    rw [PositiveLagrangianFrame.quadraticMatrix, conjTranspose_mul]
  have he : P.position⁻¹ᴴ *
      (Complex.I • (-(P.positionᴴ * P.momentum) + P.momentumᴴ * P.position)) * P.position⁻¹ =
      Complex.I • (P.quadraticMatrixᴴ - P.quadraticMatrix) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg,
      Matrix.neg_mul, hleft, hright]
    congr 1
    exact neg_add_eq_sub _ _
  rwa [he] at h

end

section

/-! Real positive-definite imaginary parts of the Gaussian matrices. -/

open _root_.Matrix
open scoped ComplexOrder

theorem symmetric_complex_imaginary_gram {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) (hZ : Z.IsSymm) :
    Complex.I • (Zᴴ - Z) = (2 : ℝ) • (Z.map Complex.im).map Complex.ofRealHom := by
  ext i j
  have hz : Z j i = Z i j := congrFun (congrFun hZ.eq i) j
  change Complex.I * (star (Z j i) - Z i j) = (2 : ℝ) • ((Z i j).im : ℂ)
  rw [hz, Complex.star_def, Complex.real_smul]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  ring

theorem real_matrix_positive_of_complexified_twice {n : ℕ}
    (Y : Matrix (Fin n) (Fin n) ℝ) (hY : Y.IsSymm)
    (hpos : ((2 : ℝ) • Y.map Complex.ofRealHom).PosDef) : Y.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (Matrix.isHermitian_iff_isSymm.mpr hY)
  intro x hx
  let xC : Fin n → ℂ := fun i => (x i : ℂ)
  have hxC : xC ≠ 0 := by
    intro h
    apply hx
    funext i
    have hi := congrFun h i
    exact Complex.ofReal_eq_zero.mp hi
  have hm : Y.map Complex.ofRealHom *ᵥ xC = fun i => ((Y *ᵥ x) i : ℂ) := by
    funext i
    exact (Complex.ofRealHom.map_mulVec Y x i).symm
  have hstar : star xC = xC := by ext i; exact Complex.conj_ofReal _
  have he : star xC ⬝ᵥ (((2 : ℝ) • Y.map Complex.ofRealHom) *ᵥ xC) =
      ((2 * (x ⬝ᵥ (Y *ᵥ x)) : ℝ) : ℂ) := by
    rw [Matrix.smul_mulVec, dotProduct_smul, hm, hstar]
    change (2 : ℝ) • ((Complex.ofRealHom ∘ x) ⬝ᵥ (Complex.ofRealHom ∘ (Y *ᵥ x))) = _
    rw [← Complex.ofRealHom.map_dotProduct]
    simp only [Complex.real_smul, Complex.ofReal_mul]
    rfl
  have h := hpos.dotProduct_mulVec_pos hxC
  rw [he] at h
  have hreal : 0 < 2 * (x ⬝ᵥ (Y *ᵥ x)) := by exact_mod_cast h
  simpa only [star_trivial] using (pos_of_mul_pos_right hreal (by norm_num : (0 : ℝ) ≤ 2))

theorem PositiveLagrangianFrame.imaginaryPart_positive {n : ℕ} (P : PositiveLagrangianFrame n) :
    (P.quadraticMatrix.map Complex.im).PosDef := by
  have hs : (P.quadraticMatrix.map Complex.im).IsSymm := P.quadraticMatrix_symmetric.map _
  apply real_matrix_positive_of_complexified_twice _ hs
  rw [← symmetric_complex_imaginary_gram P.quadraticMatrix P.quadraticMatrix_symmetric]
  exact P.quadraticMatrix_positive

end

section

/-! Simultaneous real congruence diagonalization with one positive-definite form. -/

open _root_.Matrix

theorem matrix_congruence_entry {k : Type} [CommSemiring k] {n : ℕ}
    (A M : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    (Aᵀ * M * A) i j = A.col i ⬝ᵥ (M *ᵥ A.col j) := by
  change A.col i ᵥ* M ⬝ᵥ A.col j = A.col i ⬝ᵥ (M *ᵥ A.col j)
  exact (dotProduct_mulVec _ _ _).symm

theorem real_simultaneous_congruence_diagonal {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) ℝ) (hX : X.IsSymm) (hY : Y.PosDef) :
    ∃ A : FunctionsMetaplectic.Construction.GeneralLinear ℝ n, ∃ d : Fin n → ℝ,
      A.valᵀ * Y * A.val = 1 ∧ A.valᵀ * X * A.val = diagonal d := by
  let := Y.toNormedAddCommGroup hY
  let := Y.toSeminormedAddCommGroup hY.posSemidef
  let := Y.toInnerProductSpace hY.posSemidef
  let T : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := Matrix.toLin' (Y⁻¹ * X)
  have hYsymm : Y.IsSymm := Matrix.isHermitian_iff_isSymm.mp hY.isHermitian
  have hYinv : Y * Y⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det Y).mp hY.isUnit)
  have hYT (x : Fin n → ℝ) : Y *ᵥ T x = X *ᵥ x := by
    change Y *ᵥ ((Y⁻¹ * X) *ᵥ x) = _
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hYinv, one_mul]
  have hvecY (x : Fin n → ℝ) : x ᵥ* Y = Y *ᵥ x := by simpa only [hYsymm.eq] using vecMul_transpose Y x
  have hvecX (x : Fin n → ℝ) : x ᵥ* X = X *ᵥ x := by simpa only [hX.eq] using vecMul_transpose X x
  have hT : T.IsSymmetric := by
    intro x y
    change (Y *ᵥ y) ⬝ᵥ star (T x) = (Y *ᵥ T y) ⬝ᵥ star x
    simp only [star_trivial]
    rw [hYT]
    calc
      _ = T x ⬝ᵥ (Y *ᵥ y) := dotProduct_comm _ _
      _ = (Y *ᵥ T x) ⬝ᵥ y := by rw [dotProduct_mulVec, hvecY]
      _ = (X *ᵥ x) ⬝ᵥ y := by rw [hYT]
      _ = (X *ᵥ y) ⬝ᵥ x := by rw [dotProduct_comm, dotProduct_mulVec, hvecX]
  have hdim : Module.finrank ℝ (Fin n → ℝ) = n := by simp
  let b := hT.eigenvectorBasis hdim
  let d := hT.eigenvalues hdim
  let e := Pi.basisFun ℝ (Fin n)
  let A : FunctionsMetaplectic.Construction.GeneralLinear ℝ n := {
    val := e.toMatrix b.toBasis
    inv := b.toBasis.toMatrix e
    val_inv := e.toMatrix_mul_toMatrix_flip b.toBasis
    inv_val := b.toBasis.toMatrix_mul_toMatrix_flip e }
  have hcol (i : Fin n) : A.val.col i = b i := by funext j; rfl
  have hb (i j : Fin n) : b i ⬝ᵥ (Y *ᵥ b j) = if i = j then 1 else 0 := by
    have h := b.inner_eq_ite i j
    change (Y *ᵥ b j) ⬝ᵥ star (b i) = _ at h
    simpa only [star_trivial, dotProduct_comm] using h
  have hXb (j : Fin n) : X *ᵥ b j = d j • (Y *ᵥ b j) := by
    rw [← hYT, hT.apply_eigenvectorBasis hdim j, Matrix.mulVec_smul]
    rfl
  refine ⟨A, d, ?_, ?_⟩
  · ext i j
    rw [matrix_congruence_entry, hcol, hcol, hb, Matrix.one_apply]
  · ext i j
    rw [matrix_congruence_entry, hcol, hcol, hXb, dotProduct_smul, hb]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]

theorem complex_simultaneous_congruence_diagonal {n : ℕ}
    (Z : Matrix (Fin n) (Fin n) ℂ) (hZ : Z.IsSymm)
    (hY : (Z.map Complex.im).PosDef) :
    ∃ A : FunctionsMetaplectic.Construction.GeneralLinear ℝ n, ∃ d : Fin n → ℝ,
      (A.val.map Complex.ofReal)ᵀ * Z * A.val.map Complex.ofReal =
        diagonal (fun i => (d i : ℂ) + Complex.I) := by
  have hX : (Z.map Complex.re).IsSymm := by
    ext i j
    exact congrArg Complex.re (congrFun (congrFun hZ.eq i) j)
  obtain ⟨A, d, hAY, hAX⟩ :=
    real_simultaneous_congruence_diagonal (Z.map Complex.re) (Z.map Complex.im) hX hY
  refine ⟨A, d, ?_⟩
  have he (i j : Fin n) :
      ((A.val.map Complex.ofReal)ᵀ * Z * A.val.map Complex.ofReal) i j =
        ((A.valᵀ * Z.map Complex.re * A.val) i j : ℂ) +
          ((A.valᵀ * Z.map Complex.im * A.val) i j : ℂ) * Complex.I := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro m _
    conv_lhs => rw [← Complex.re_add_im (Z m l)]
    ring
  ext i j
  rw [he, hAX, hAY]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

end

section

/-! Ordinary convergent scalar Gaussians for the real Siegel half-space. -/

open _root_.MeasureTheory

def siegelGaussianScalar (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (Real.pi * Complex.I * z * (x : ℂ) ^ 2)

def siegelGaussianCoefficient (z : ℂ) : ℂ :=
  (Complex.I / z) ^ (1 / 2 : ℂ)

theorem siegelGaussianScalar_eq (z : ℂ) (x : ℝ) :
    siegelGaussianScalar z x =
      Complex.exp (-(-(Real.pi : ℂ) * Complex.I * z) * (x : ℂ) ^ 2) := by
  unfold siegelGaussianScalar
  congr 1
  ring

theorem siegelGaussianScalar_norm (z : ℂ) (x : ℝ) :
    ‖siegelGaussianScalar z x‖ = Real.exp (-(Real.pi * z.im) * x ^ 2) := by
  rw [siegelGaussianScalar_eq, norm_cexp_neg_mul_sq]
  simp

theorem siegelGaussianScalar_integrable {z : ℂ} (hz : 0 < z.im) :
    Integrable (siegelGaussianScalar z) := by
  have hb : 0 < (-(Real.pi : ℂ) * Complex.I * z).re := by
    simpa using mul_pos Real.pi_pos hz
  simpa only [← siegelGaussianScalar_eq] using integrable_cexp_neg_mul_sq hb

theorem siegelGaussianScalar_memLp_two {z : ℂ} (hz : 0 < z.im) :
    MemLp (siegelGaussianScalar z) 2 := by
  apply (memLp_two_iff_integrable_sq_norm (by unfold siegelGaussianScalar; fun_prop)).mpr
  have he (x : ℝ) : ‖siegelGaussianScalar z x‖ ^ 2 =
      Real.exp (-(2 * (Real.pi * z.im)) * x ^ 2) := by
    rw [siegelGaussianScalar_norm, ← Real.exp_nat_mul]
    congr 1
    ring
  simp_rw [he]
  exact integrable_exp_neg_mul_sq (mul_pos (by norm_num) (mul_pos Real.pi_pos hz))

theorem siegelGaussianCoefficient_sq {z : ℂ} (hz : z ≠ 0) :
    siegelGaussianCoefficient z ^ 2 * z = Complex.I := by
  rw [siegelGaussianCoefficient, one_div, Complex.cpow_ofNat_inv_pow]
  exact div_mul_cancel₀ _ hz

theorem siegelGaussianCoefficient_ne_zero {z : ℂ} (hz : z ≠ 0) :
    siegelGaussianCoefficient z ≠ 0 := by
  intro h
  have he := siegelGaussianCoefficient_sq hz
  rw [h, zero_pow (by decide), zero_mul] at he
  exact Complex.I_ne_zero he.symm

theorem scalarFourier_siegelGaussian {z : ℂ} (hz : 0 < z.im) (x : ℝ) :
    FourierTensor.Construction.scalarFourierIntegral (Gaussian.Construction.realCharacter 1) volume (siegelGaussianScalar z) x =
      siegelGaussianCoefficient z * siegelGaussianScalar (-z⁻¹) x := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hb : 0 < (-(Real.pi : ℂ) * Complex.I * z).re := by
    simpa using mul_pos Real.pi_pos hz
  unfold FourierTensor.Construction.scalarFourierIntegral
  simp_rw [siegelGaussianScalar, Gaussian.Construction.realCharacter_apply]
  have hk (y : ℝ) : (((2 * Real.pi * 1 * -(x * y) : ℝ) : ℂ) * Complex.I) =
      Complex.I * (-2 * Real.pi * x : ℂ) * y := by push_cast; ring
  have hg (y : ℝ) : (Real.pi : ℂ) * Complex.I * z * (y : ℂ) ^ 2 =
      -(-(Real.pi : ℂ) * Complex.I * z) * (y : ℂ) ^ 2 := by ring
  simp_rw [hk, hg]
  conv_lhs => enter [2, y]; rw [mul_comm]
  rw [fourierIntegral_gaussian hb]
  have hc : (Real.pi : ℂ) / (-(Real.pi : ℂ) * Complex.I * z) = Complex.I / z := by
    field_simp
    simp [Complex.I_sq]
  rw [hc]
  unfold siegelGaussianCoefficient
  congr 2
  field_simp
  simp [Complex.I_sq]
  ring

end

section

/-! Quadratic Gaussians and real changes of coordinates. -/

open _root_.Matrix _root_.MeasureTheory

def siegelGaussian {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) (x : FunctionsMetaplectic.Construction.Position ℝ n) : ℂ :=
  Complex.exp (Real.pi * Complex.I * ((fun i => (x i : ℂ)) ⬝ᵥ
    (Z *ᵥ fun i => (x i : ℂ))))

theorem complexify_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    (fun i => ((A *ᵥ x) i : ℂ)) = A.map Complex.ofReal *ᵥ fun i => (x i : ℂ) := by
  ext i
  exact RingHom.map_mulVec Complex.ofRealHom A x i

theorem siegelGaussian_congruence {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (Z : Matrix (Fin n) (Fin n) ℂ) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    siegelGaussian Z (A *ᵥ x) =
      siegelGaussian ((A.map Complex.ofReal)ᵀ * Z * A.map Complex.ofReal) x := by
  unfold siegelGaussian
  rw [complexify_mulVec]
  congr 2
  nth_rw 1 [← vecMul_transpose]
  rw [dotProduct_mulVec, vecMul_vecMul, ← dotProduct_mulVec, mulVec_mulVec]

theorem siegelGaussian_diagonal {n : ℕ} (z : Fin n → ℂ) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    siegelGaussian (diagonal z) x = ∏ i, siegelGaussianScalar (z i) (x i) := by
  unfold siegelGaussian siegelGaussianScalar
  rw [← Complex.exp_sum]
  congr 1
  simp only [dotProduct, mulVec_diagonal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem siegelGaussian_continuous {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (siegelGaussian Z) := by
  unfold siegelGaussian Matrix.mulVec dotProduct
  fun_prop

theorem siegelGaussian_zero {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ) :
    siegelGaussian Z 0 = 1 := by
  simp [siegelGaussian]

theorem real_integral_matrix {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (A : FunctionsMetaplectic.Construction.GeneralLinear ℝ n) (f : FunctionsMetaplectic.Construction.Position ℝ n → E) :
    (∫ x, f (A.val *ᵥ x)) = |det A.val|⁻¹ • ∫ x, f x := by
  let e := (LinearSubstitution.Construction.positionAddEquiv A).toHomeomorph.toMeasurableEquiv
  have hd : LinearMap.det (LinearSubstitution.Construction.positionLinearEquiv A).toLinearMap = det A.val := by
    change LinearMap.det (Matrix.toLin' A.val) = _
    exact LinearMap.det_toLin' _
  have hm := Measure.map_linearMap_addHaar_pi_eq_smul_addHaar
    (show LinearMap.det (LinearSubstitution.Construction.positionLinearEquiv A).toLinearMap ≠ 0 by
      rw [hd]; exact (FunctionsMetaplectic.Construction.determinantUnit ℝ A).ne_zero) (volume : Measure (FunctionsMetaplectic.Construction.Position ℝ n))
  have hi := integral_map_equiv (μ := (volume : Measure (FunctionsMetaplectic.Construction.Position ℝ n))) e f
  change (∫ x, f x ∂Measure.map (LinearSubstitution.Construction.positionLinearEquiv A).toLinearMap volume) = _ at hi
  rw [hm, hd, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv] at hi
  exact hi.symm

theorem real_integrable_matrix_iff {E : Type} [NormedAddCommGroup E]
    {n : ℕ} (A : FunctionsMetaplectic.Construction.GeneralLinear ℝ n) (f : FunctionsMetaplectic.Construction.Position ℝ n → E) :
    Integrable (fun x => f (A.val *ᵥ x)) ↔ Integrable f := by
  let e := (LinearSubstitution.Construction.positionAddEquiv A).toHomeomorph.toMeasurableEquiv
  have hd : LinearMap.det (LinearSubstitution.Construction.positionLinearEquiv A).toLinearMap = det A.val := by
    change LinearMap.det (Matrix.toLin' A.val) = _
    exact LinearMap.det_toLin' _
  have hm := Measure.map_linearMap_addHaar_pi_eq_smul_addHaar
    (show LinearMap.det (LinearSubstitution.Construction.positionLinearEquiv A).toLinearMap ≠ 0 by
      rw [hd]; exact (FunctionsMetaplectic.Construction.determinantUnit ℝ A).ne_zero) (volume : Measure (FunctionsMetaplectic.Construction.Position ℝ n))
  have hi := integrable_map_equiv (μ := (volume : Measure (FunctionsMetaplectic.Construction.Position ℝ n))) e f
  change Integrable f (Measure.map (LinearSubstitution.Construction.positionLinearEquiv A).toLinearMap volume) ↔ _ at hi
  have hdet : det A.val ≠ 0 := (FunctionsMetaplectic.Construction.determinantUnit ℝ A).ne_zero
  rw [hm, hd, integrable_smul_measure (by simp [hdet]) (by simp)] at hi
  exact hi.symm

theorem siegelGaussian_integrable {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ)
    (hZ : Z.IsSymm) (hY : (Z.map Complex.im).PosDef) : Integrable (siegelGaussian Z) := by
  obtain ⟨A, d, hd⟩ := complex_simultaneous_congruence_diagonal Z hZ hY
  apply (real_integrable_matrix_iff A _).mp
  change Integrable (fun x => siegelGaussian Z (A.val *ᵥ x))
  simp_rw [siegelGaussian_congruence, hd, siegelGaussian_diagonal]
  exact Integrable.fintype_prod (fun i => siegelGaussianScalar_integrable (by simp))

theorem siegelGaussian_memLp_two {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ)
    (hZ : Z.IsSymm) (hY : (Z.map Complex.im).PosDef) : MemLp (siegelGaussian Z) 2 := by
  apply (memLp_two_iff_integrable_sq_norm (siegelGaussian_continuous Z).aestronglyMeasurable).mpr
  obtain ⟨A, d, hd⟩ := complex_simultaneous_congruence_diagonal Z hZ hY
  apply (real_integrable_matrix_iff A _).mp
  change Integrable (fun x => ‖siegelGaussian Z (A.val *ᵥ x)‖ ^ 2)
  simp_rw [siegelGaussian_congruence, hd, siegelGaussian_diagonal, norm_prod, ← Finset.prod_pow]
  exact Integrable.fintype_prod (fun i =>
    (siegelGaussianScalar_memLp_two (z := (d i : ℂ) + Complex.I) (by simp)).integrable_norm_pow
      (by decide : (2 : ℕ) ≠ 0))

end

/-! The convergent matrix Gaussian Fourier integral, with its determinant identity. -/

open _root_.Matrix _root_.MeasureTheory

theorem fourierIntegral_real_matrix {n : ℕ} (ψ : AddChar ℝ ℂ)
    (A : FunctionsMetaplectic.Construction.GeneralLinear ℝ n) (f : FunctionsMetaplectic.Construction.Position ℝ n → ℂ) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ volume f x = ((|det A.val| : ℝ) : ℂ) *
      FunctionsMetaplectic.Construction.fourierIntegral ψ volume (fun y => f (A.val *ᵥ y)) (A.valᵀ *ᵥ x) := by
  have h := real_integral_matrix A (fun y => f y * ψ (-FunctionsMetaplectic.Construction.dot x y))
  have hd : ((|det A.val| : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast abs_ne_zero.mpr (FunctionsMetaplectic.Construction.determinantUnit ℝ A).ne_zero
  have hdot (y : FunctionsMetaplectic.Construction.Position ℝ n) : FunctionsMetaplectic.Construction.dot x (A.val *ᵥ y) = FunctionsMetaplectic.Construction.dot (A.valᵀ *ᵥ x) y := by
    change x ⬝ᵥ (A.val *ᵥ y) = (A.valᵀ *ᵥ x) ⬝ᵥ y
    rw [dotProduct_mulVec, ← vecMul_transpose, transpose_transpose]
  simp_rw [hdot] at h
  change FunctionsMetaplectic.Construction.fourierIntegral ψ volume (fun y => f (A.val *ᵥ y)) (A.valᵀ *ᵥ x) =
    |det A.val|⁻¹ • FunctionsMetaplectic.Construction.fourierIntegral ψ volume f x at h
  rw [h, Complex.real_smul, Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]

theorem inverse_congruence {n : ℕ} (A Z D : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUnit A) (h : Aᵀ * Z * A = D) : Z⁻¹ = A * D⁻¹ * Aᵀ := by
  have hd : IsUnit A.det := (isUnit_iff_isUnit_det A).mp hA
  have ht : IsUnit Aᵀ.det := by simpa only [det_transpose] using hd
  have hi := congrArg (fun M => A * M⁻¹ * Aᵀ) h
  simpa only [Matrix.mul_inv_rev, Matrix.mul_assoc, nonsing_inv_mul _ ht, mul_one,
    mul_nonsing_inv_cancel_left _ _ hd] using hi

theorem complexify_isUnit {n : ℕ} (A : FunctionsMetaplectic.Construction.GeneralLinear ℝ n) :
    IsUnit (A.val.map Complex.ofReal) := by
  apply (isUnit_iff_isUnit_det _).mpr
  change IsUnit (Complex.ofRealHom.mapMatrix A.val).det
  rw [← RingHom.map_det Complex.ofRealHom]
  exact IsUnit.map Complex.ofRealHom ((isUnit_iff_isUnit_det _).mp A.isUnit)

theorem siegelGaussian_fourier_diagonal {n : ℕ} (z : Fin n → ℂ)
    (hz : ∀ i, 0 < (z i).im) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter 1) volume (siegelGaussian (diagonal z)) x =
      (∏ i, siegelGaussianCoefficient (z i)) *
        siegelGaussian (diagonal (fun i => -(z i)⁻¹)) x := by
  change FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter 1) (Measure.pi fun _ : Fin n => volume) _ _ = _
  simp_rw [show siegelGaussian (diagonal z) = fun y => ∏ i, siegelGaussianScalar (z i) (y i)
    from funext (siegelGaussian_diagonal z)]
  rw [FourierTensor.Construction.fourierIntegral_product]
  simp_rw [scalarFourier_siegelGaussian (hz _)]
  rw [Finset.prod_mul_distrib, siegelGaussian_diagonal]

theorem siegelGaussian_fourier_of_congruence {n : ℕ}
    (Z : Matrix (Fin n) (Fin n) ℂ) (A : FunctionsMetaplectic.Construction.GeneralLinear ℝ n) (z : Fin n → ℂ)
    (hz : ∀ i, 0 < (z i).im)
    (h : (A.val.map Complex.ofReal)ᵀ * Z * A.val.map Complex.ofReal = diagonal z)
    (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter 1) volume (siegelGaussian Z) x =
      (((|det A.val| : ℝ) : ℂ) * ∏ i, siegelGaussianCoefficient (z i)) * siegelGaussian (-Z⁻¹) x := by
  rw [fourierIntegral_real_matrix _ A]
  simp_rw [siegelGaussian_congruence, h]
  rw [siegelGaussian_fourier_diagonal z hz, mul_assoc]
  congr 1
  congr 1
  rw [siegelGaussian_congruence]
  congr 1
  have hi := inverse_congruence _ _ _ (complexify_isUnit A) h
  have hdi : (diagonal z)⁻¹ = diagonal (fun i => (z i)⁻¹) := by
    apply inv_eq_left_inv
    rw [diagonal_mul_diagonal]
    have hz0 (i : Fin n) : z i ≠ 0 := by
      intro hi
      have hp := hz i
      simp [hi] at hp
    simp only [inv_mul_cancel₀ (hz0 _), diagonal_one]
  rw [hi, hdi]
  simp only [← diagonal_neg, Matrix.mul_neg, Matrix.neg_mul]
  rfl

theorem siegelGaussian_amplitude_square {n : ℕ}
    (Z : Matrix (Fin n) (Fin n) ℂ) (A : FunctionsMetaplectic.Construction.GeneralLinear ℝ n) (z : Fin n → ℂ)
    (hz : ∀ i, z i ≠ 0)
    (h : (A.val.map Complex.ofReal)ᵀ * Z * A.val.map Complex.ofReal = diagonal z) :
    (((|det A.val| : ℝ) : ℂ) * ∏ i, siegelGaussianCoefficient (z i)) ^ 2 * det Z = Complex.I ^ n := by
  have hd := congrArg Matrix.det h
  have hdA : det (A.val.map Complex.ofReal) = ((det A.val : ℝ) : ℂ) :=
    (RingHom.map_det Complex.ofRealHom A.val).symm
  simp only [det_mul, det_transpose, hdA, det_diagonal] at hd
  have hs : ((|det A.val| : ℝ) : ℂ) ^ 2 = ((det A.val : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs]
  calc
    _ = (∏ i, siegelGaussianCoefficient (z i) ^ 2) *
        (((det A.val : ℝ) : ℂ) * det Z * ((det A.val : ℝ) : ℂ)) := by
      rw [mul_pow, hs, Finset.prod_pow]
      ring
    _ = ∏ i, siegelGaussianCoefficient (z i) ^ 2 * z i := by
      rw [hd, Finset.prod_mul_distrib]
    _ = Complex.I ^ n := by
      simp only [siegelGaussianCoefficient_sq (hz _), Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]

theorem siegelGaussian_fourier {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ)
    (hZ : Z.IsSymm) (hY : (Z.map Complex.im).PosDef) :
    ∃ c : ℂ, c ^ 2 * det Z = Complex.I ^ n ∧
      ∀ x, FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter 1) volume (siegelGaussian Z) x =
        c * siegelGaussian (-Z⁻¹) x := by
  obtain ⟨A, d, hd⟩ := complex_simultaneous_congruence_diagonal Z hZ hY
  refine ⟨((|det A.val| : ℝ) : ℂ) * ∏ i, siegelGaussianCoefficient ((d i : ℂ) + Complex.I),
    siegelGaussian_amplitude_square Z A _ (fun i => ?_) hd,
    siegelGaussian_fourier_of_congruence Z A _ (fun i => by simp) hd⟩
  intro h
  have hi := congrArg Complex.im h
  simp at hi

end

end OAI.RepresentationTheory.Weil.Local.SiegelGaussian.Construction
