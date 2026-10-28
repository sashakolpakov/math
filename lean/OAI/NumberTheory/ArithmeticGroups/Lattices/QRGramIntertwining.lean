import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRVal
import OAI.NumberTheory.ArithmeticGroups.Lattices.SpectralOperatorExponential

/-! # QR Gram Intertwining -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.QRGramIntertwining.Construction

noncomputable section

section

/-! Gram--Schmidt and QR preserve mutually orthogonal weight blocks. -/

open InnerProductSpace
open scoped Classical

theorem gramSchmidt_weight_blocks
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L]
    {n : ℕ} {α : Type*} (w : Fin n → α) (f : Fin n → L)
    (hf : ∀ i j, w i ≠ w j → inner ℝ (f i) (f j) = 0) :
    ∀ i j, w i ≠ w j → inner ℝ (gramSchmidt ℝ f i) (f j) = 0 := by
  intro i
  induction i using (wellFounded_lt (α := Fin n)).induction with
  | h i ih =>
    intro j hij
    have hrec : gramSchmidt ℝ f i = f i -
        ∑ k ∈ Finset.Iio i,
          (inner ℝ (gramSchmidt ℝ f k) (f i) / ‖gramSchmidt ℝ f k‖ ^ 2) •
            gramSchmidt ℝ f k := by
      rw [eq_sub_iff_add_eq]
      exact (gramSchmidt_def'' ℝ f i).symm
    rw [hrec, inner_sub_left, sum_inner, hf i j hij]
    suffices hs : ∑ k ∈ Finset.Iio i,
        inner ℝ ((inner ℝ (gramSchmidt ℝ f k) (f i) / ‖gramSchmidt ℝ f k‖ ^ 2) •
          gramSchmidt ℝ f k) (f j) = 0 by simp only [hs, sub_zero]
    apply Finset.sum_eq_zero
    intro k hk
    rw [real_inner_smul_left]
    by_cases hki : w k = w i
    · rw [ih k (Finset.mem_Iio.mp hk) j (hki ▸ hij), mul_zero]
    · rw [ih k (Finset.mem_Iio.mp hk) i hki, zero_div, zero_mul]

theorem operatorQR_unipotent_weight_blocks
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} {α : Type*} (b : OrthonormalBasis (Fin m) ℝ L)
    (g : (L →L[ℝ] L)ˣ) (w : Fin m → α)
    (hg : ∀ i j, w i ≠ w j → inner ℝ (g.val (b i)) (g.val (b j)) = 0)
    (i j : Fin m) (hij : w i ≠ w j) : OperatorQRVal.Construction.operatorQRUnipotentMatrix b g i j = 0 := by
  rw [OperatorQRVal.Construction.operatorQRUnipotentMatrix_entry, OperatorQRVal.Construction.operatorQRTriangularMatrix_entry]
  have hi : gramSchmidtNormed ℝ (fun k => g.val (b k)) i ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [gramSchmidtNormed_unit_length i (OperatorQRBasis.Construction.operatorFrame_linearIndependent b g)]
    exact one_ne_zero
  rw [OperatorQRBasis.Construction.operatorQRBasis, gramSchmidtOrthonormalBasis_apply _ hi]
  unfold gramSchmidtNormed
  rw [real_inner_smul_left, gramSchmidt_weight_blocks w _ hg i j hij, mul_zero, mul_zero]

theorem operatorQR_unipotent_commutes_weight_diagonal
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (g : (L →L[ℝ] L)ˣ) (w : Fin m → ℝ)
    (hg : ∀ i j, w i ≠ w j → inner ℝ (g.val (b i)) (g.val (b j)) = 0) :
    Commute (OperatorQRVal.Construction.operatorQRUnipotentMatrix b g) (Matrix.diagonal w) := by
  change OperatorQRVal.Construction.operatorQRUnipotentMatrix b g * Matrix.diagonal w =
    Matrix.diagonal w * OperatorQRVal.Construction.operatorQRUnipotentMatrix b g
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : w i = w j
  · rw [hij, mul_comm]
  · rw [operatorQR_unipotent_weight_blocks b g w hg i j hij, zero_mul, mul_zero]

end

section

/-! When the columns of an operator are eigenvectors of a symmetric
operator, its unipotent QR factor commutes with their weight diagonal. -/

theorem symmetric_eigenvectors_inner_zero
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L]
    (A : L →L[ℝ] L) (hA : A.toLinearMap.IsSymmetric)
    (x y : L) (a b : ℝ) (hx : A x = a • x) (hy : A y = b • y) (hab : a ≠ b) :
    inner ℝ x y = 0 := by
  have he := hA x y
  change inner ℝ (A x) y = inner ℝ x (A y) at he
  rw [hx, hy, real_inner_smul_left, real_inner_smul_right] at he
  have hz : (a - b) * inner ℝ x y = 0 := by nlinarith
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hab)

theorem operatorQR_unipotent_commutes_diagonal_of_eigenvectors
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (g : (L →L[ℝ] L)ˣ)
    (A : L →L[ℝ] L) (hA : A.toLinearMap.IsSymmetric) (w : Fin m → ℝ)
    (heig : ∀ i, A (g.val (b i)) = w i • g.val (b i)) :
    Commute (OperatorQRVal.Construction.operatorQRUnipotentMatrix b g) (Matrix.diagonal w) := by
  apply operatorQR_unipotent_commutes_weight_diagonal b g w
  intro i j hij
  exact symmetric_eigenvectors_inner_zero A hA _ _ _ _ (heig i) (heig j) hij

end

/-! Matrix intertwining with real diagonal operators forces the
unipotent QR factor to preserve every function of the input diagonal. -/

theorem commute_diagonal_function {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ)
    (hM : Commute M (Matrix.diagonal w)) (f : ℝ → ℝ) :
    Commute M (Matrix.diagonal (fun i => f (w i))) := by
  change M * Matrix.diagonal (fun i => f (w i)) = Matrix.diagonal (fun i => f (w i)) * M
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : w i = w j
  · rw [hij, mul_comm]
  · have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) hM.eq
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at he
    have hz : (w i - w j) * M i j = 0 := by nlinarith
    have h0 := (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hij)
    rw [h0, zero_mul, mul_zero]

theorem operatorQR_unipotent_commutes_of_matrix_intertwining
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (g : (L →L[ℝ] L)ˣ) (x y : Fin m → ℝ)
    (hxy : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis g.val * Matrix.diagonal y =
      Matrix.diagonal x * ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis g.val) (f : ℝ → ℝ) :
    Commute (OperatorQRVal.Construction.operatorQRUnipotentMatrix b g) (Matrix.diagonal (fun i => f (y i))) := by
  let A : L →L[ℝ] L := (BasisSpectralOperator.Construction.basisSpectralEnd b.toBasis x).toContinuousLinearMap
  let C : L →L[ℝ] L := (BasisSpectralOperator.Construction.basisSpectralEnd b.toBasis y).toContinuousLinearMap
  have hA : A.toLinearMap.IsSymmetric := BasisSpectralOperator.Construction.basisSpectralEnd_isSymmetric b x
  have hAM : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis A = Matrix.diagonal x :=
    SpectralOperatorExponential.Construction.basisSpectralEnd_toMatrix b.toBasis x
  have hCM : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis C = Matrix.diagonal y :=
    SpectralOperatorExponential.Construction.basisSpectralEnd_toMatrix b.toBasis y
  have he : A * g.val = g.val * C := by
    apply (ContinuousEndMatrixEquiv.Construction.continuousEndMatrix_bijective b.toBasis).1
    rw [map_mul, map_mul, hAM, hCM]
    exact hxy.symm
  have heig : ∀ i, A (g.val (b i)) = y i • g.val (b i) := by
    intro i
    have hi := congrArg (fun T : L →L[ℝ] L => T (b i)) he
    change A (g.val (b i)) = g.val (C (b i)) at hi
    rw [show C (b i) = y i • b i from BasisSpectralOperator.Construction.basisSpectralEnd_apply_basis b.toBasis y i, map_smul] at hi
    exact hi
  exact commute_diagonal_function _ y
    (operatorQR_unipotent_commutes_diagonal_of_eigenvectors b g A hA y heig) f

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.QRGramIntertwining.Construction
