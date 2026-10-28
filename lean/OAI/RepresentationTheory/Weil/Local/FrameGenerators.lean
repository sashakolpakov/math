import OAI.RepresentationTheory.Weil.Local.SiegelGaussian

/-! # Frame Generators -/

namespace OAI.RepresentationTheory.Weil.Local

noncomputable section

/-! The actual lower and Weyl generators act on positive Gaussian frames. -/

open _root_.Matrix

theorem SiegelGaussian.Construction.PositiveLagrangianFrame.lower_matrix {n : ℕ} (P : SiegelGaussian.Construction.PositiveLagrangianFrame n)
    (B : FunctionsMetaplectic.Construction.SymmetricMatrix ℝ n) :
    (P.act (Generators.Construction.quadraticSymplectic B)).matrix =
      Matrix.fromRows P.position (B.val.map Complex.ofReal * P.position + P.momentum) := by
  change (Generators.Construction.quadraticSymplectic B).val.map Complex.ofReal * P.matrix = _
  rw [Generators.Construction.quadraticSymplectic_matrix, ← P.fromRows, fromBlocks_map]
  simp only [Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one,
    Matrix.map_zero _ Complex.ofReal_zero, fromBlocks_mul_fromRows, one_mul,
    zero_mul, add_zero]

theorem SiegelGaussian.Construction.PositiveLagrangianFrame.lower_position {n : ℕ} (P : SiegelGaussian.Construction.PositiveLagrangianFrame n)
    (B : FunctionsMetaplectic.Construction.SymmetricMatrix ℝ n) : (P.act (Generators.Construction.quadraticSymplectic B)).position = P.position := by
  unfold SiegelGaussian.Construction.PositiveLagrangianFrame.position
  rw [P.lower_matrix]
  rfl

theorem SiegelGaussian.Construction.PositiveLagrangianFrame.lower_momentum {n : ℕ} (P : SiegelGaussian.Construction.PositiveLagrangianFrame n)
    (B : FunctionsMetaplectic.Construction.SymmetricMatrix ℝ n) : (P.act (Generators.Construction.quadraticSymplectic B)).momentum =
      B.val.map Complex.ofReal * P.position + P.momentum := by
  unfold SiegelGaussian.Construction.PositiveLagrangianFrame.momentum
  rw [P.lower_matrix]
  rfl

theorem SiegelGaussian.Construction.PositiveLagrangianFrame.lower_quadraticMatrix {n : ℕ} (P : SiegelGaussian.Construction.PositiveLagrangianFrame n)
    (B : FunctionsMetaplectic.Construction.SymmetricMatrix ℝ n) : (P.act (Generators.Construction.quadraticSymplectic B)).quadraticMatrix =
      B.val.map Complex.ofReal + P.quadraticMatrix := by
  rw [SiegelGaussian.Construction.PositiveLagrangianFrame.quadraticMatrix, P.lower_position, P.lower_momentum, Matrix.add_mul,
    Matrix.mul_assoc, P.position_mul_inv, mul_one]
  rfl

theorem SiegelGaussian.Construction.PositiveLagrangianFrame.weyl_matrix {n : ℕ} (P : SiegelGaussian.Construction.PositiveLagrangianFrame n) :
    (P.act (Generators.Construction.weylSymplectic ℝ n)).matrix = Matrix.fromRows P.momentum (-P.position) := by
  change (Generators.Construction.weylSymplectic ℝ n).val.map Complex.ofReal * P.matrix = _
  rw [Generators.Construction.weylSymplectic_matrix, ← P.fromRows, fromBlocks_map]
  simp only [Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one,
    Matrix.map_zero _ Complex.ofReal_zero, Matrix.map_neg _ Complex.ofReal_neg,
    fromBlocks_mul_fromRows, one_mul, zero_mul, add_zero, zero_add, neg_mul]

theorem SiegelGaussian.Construction.PositiveLagrangianFrame.weyl_position {n : ℕ} (P : SiegelGaussian.Construction.PositiveLagrangianFrame n) :
    (P.act (Generators.Construction.weylSymplectic ℝ n)).position = P.momentum := by
  unfold SiegelGaussian.Construction.PositiveLagrangianFrame.position
  rw [P.weyl_matrix]
  rfl

theorem SiegelGaussian.Construction.PositiveLagrangianFrame.weyl_momentum {n : ℕ} (P : SiegelGaussian.Construction.PositiveLagrangianFrame n) :
    (P.act (Generators.Construction.weylSymplectic ℝ n)).momentum = -P.position := by
  unfold SiegelGaussian.Construction.PositiveLagrangianFrame.momentum
  rw [P.weyl_matrix]
  rfl

theorem SiegelGaussian.Construction.PositiveLagrangianFrame.momentum_isUnit {n : ℕ} (P : SiegelGaussian.Construction.PositiveLagrangianFrame n) :
    IsUnit P.momentum := by
  rw [← P.weyl_position]
  exact (P.act (Generators.Construction.weylSymplectic ℝ n)).position_isUnit

theorem SiegelGaussian.Construction.PositiveLagrangianFrame.weyl_quadraticMatrix {n : ℕ} (P : SiegelGaussian.Construction.PositiveLagrangianFrame n) :
    (P.act (Generators.Construction.weylSymplectic ℝ n)).quadraticMatrix = -P.quadraticMatrix⁻¹ := by
  rw [SiegelGaussian.Construction.PositiveLagrangianFrame.quadraticMatrix, P.weyl_position, P.weyl_momentum, Matrix.neg_mul]
  congr 1
  rw [SiegelGaussian.Construction.PositiveLagrangianFrame.quadraticMatrix, Matrix.mul_inv_rev,
    Matrix.nonsing_inv_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp P.position_isUnit)]

theorem SiegelGaussian.Construction.PositiveLagrangianFrame.quadraticMatrix_isUnit {n : ℕ} (P : SiegelGaussian.Construction.PositiveLagrangianFrame n) :
    IsUnit P.quadraticMatrix :=
  P.momentum_isUnit.mul (Matrix.isUnit_nonsing_inv_iff.mpr P.position_isUnit)

theorem SiegelGaussian.Construction.PositiveLagrangianFrame.weyl_position_det {n : ℕ} (P : SiegelGaussian.Construction.PositiveLagrangianFrame n) :
    (P.act (Generators.Construction.weylSymplectic ℝ n)).position.det = P.quadraticMatrix.det * P.position.det := by
  rw [P.weyl_position, ← det_mul, SiegelGaussian.Construction.PositiveLagrangianFrame.quadraticMatrix, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp P.position_isUnit), mul_one]

theorem FrameGenerators.Construction.siegelGaussian_quadratic_mul {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin n) ℝ) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    Gaussian.Construction.realCharacter 1 (FunctionsMetaplectic.Construction.quadratic B x) * SiegelGaussian.Construction.siegelGaussian Z x =
      SiegelGaussian.Construction.siegelGaussian (B.map Complex.ofReal + Z) x := by
  rw [Gaussian.Construction.realCharacter_apply, SiegelGaussian.Construction.siegelGaussian, SiegelGaussian.Construction.siegelGaussian, ← Complex.exp_add,
    Matrix.add_mulVec, dotProduct_add, mul_add]
  congr 1
  congr 1
  unfold FunctionsMetaplectic.Construction.quadratic Matrix.mulVec dotProduct
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat,
    Complex.ofReal_one, Complex.ofReal_sum, Matrix.map_apply, Finset.mul_sum]
  have he (s : ℂ) : 2 * Real.pi * 1 * (s / 2) * Complex.I = Real.pi * Complex.I * s := by ring
  rw [he]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end

end OAI.RepresentationTheory.Weil.Local
