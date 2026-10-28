import OAI.RepresentationTheory.Theta.Kernel.IntrinsicBlockSiegel
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSchwartz
import OAI.RepresentationTheory.Theta.Adelic.DataTheta

/-! # Intrinsic Block Completion -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Kernel.IntrinsicBlockCompletion.IntrinsicKernel

/-! Literal native theta kernels in the coordinates constructed from the
two summands. The block identity is proved by reindexing the rational sum
and evaluating actual restricted-tensor Schwartz inputs. -/

open scoped _root_.NumberField Classical _root_.Matrix BigOperators _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Kernel.IntrinsicSchwartz.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicBlockSiegel.Intrinsic

variable (F : Type) [Field F] [NumberField F]

def positionSplit : (Fin 6 → F) ≃ₗ[F] ((Fin 3 → F) × (Fin 3 → F)) :=
  (LinearEquiv.piCongrLeft F (fun _ : Fin 6 => F) finSumFinEquiv).symm.trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin 3) (Fin 3) F F)

omit [NumberField F] in
theorem positionSplit_left (x : Fin 6 → F) (i : Fin 3) :
    (positionSplit F x).1 i = x (Fin.castAdd 3 i) := rfl

omit [NumberField F] in
theorem positionSplit_right (x : Fin 6 → F) (i : Fin 3) :
    (positionSplit F x).2 i = x (Fin.natAdd 3 i) := rfl

variable {F}
variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def blockPosition (R₁ : (Fin 3 → F) ≃ₗ[ℚ] (I → ℚ))
    (R₂ : (Fin 3 → F) ≃ₗ[ℚ] (J → ℚ)) : (Fin 6 → F) ≃ₗ[ℚ] ((I ⊕ J) → ℚ) :=
  ((positionSplit F).restrictScalars ℚ).trans
    ((R₁.prodCongr R₂).trans (LinearEquiv.sumArrowLequivProdArrow I J ℚ ℚ).symm)

def kernel (Z : Matrix I I ℂ) (ξ : I → ℂ) (x : I → ℝ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm Z x x +
    (2 * (Real.pi : ℂ) * Complex.I) * ∑ i, (x i : ℂ) * ξ i)

def literalTheta {n : ℕ} (R : (Fin n → F) ≃ₗ[ℚ] (I → ℚ))
    (f : Adelic.FiniteSchwartz.finiteSchwartz F n) (Z : Matrix I I ℂ) (ξ : I → ℂ) : ℂ :=
  ∑' x : Fin n → F,
    Adelic.Evaluation.finiteSchwartzFunction F n f (fun i => algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) (x i)) *
      kernel Z ξ (fun i => (R x i : ℝ))

def literalCompleted {n : ℕ} (R : (Fin n → F) ≃ₗ[ℚ] (I → ℚ))
    (f : Adelic.FiniteSchwartz.finiteSchwartz F n) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (ξ : I → ℂ) : ℂ :=
  AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor (((Real.pi : ℂ) / 2) •
    AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear ((AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary Z.matrix)⁻¹)) ξ * literalTheta R f Z.matrix ξ

omit [DecidableEq I] [DecidableEq J] in
theorem kernel_blocks (Z₁ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (Z₂ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix J)
    (ξ₁ : I → ℂ) (ξ₂ : J → ℂ) (x₁ : I → ℝ) (x₂ : J → ℝ) :
    kernel (IntrinsicBlockSiegel.Intrinsic.blockPeriod Z₁ Z₂).matrix (Sum.elim ξ₁ ξ₂) (Sum.elim x₁ x₂) =
      kernel Z₁.matrix ξ₁ x₁ * kernel Z₂.matrix ξ₂ x₂ := by
  simp only [kernel, IntrinsicBlockSiegel.Intrinsic.blockPeriod, AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm_apply, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
    mul_zero, Finset.sum_const_zero, zero_add, add_zero, Finset.sum_add_distrib]
  rw [← Complex.exp_add]
  congr 1
  ring

variable {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ K₂ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A₁ : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁} {A₂ : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₂}
variable (B₁ : Adelic.DataTheta.ComparisonData F H K₁ A₁) (B₂ : Adelic.DataTheta.ComparisonData F H K₂ A₂)

theorem literalTheta_native (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 1))
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Adelic.BallGeometryData.FrameIndex A₁)) (ξ : Adelic.BallGeometryData.FrameIndex A₁ → ℂ) :
    literalTheta B₁.rationalPosition f Z.matrix ξ = Adelic.DataTheta.rationalTheta B₁ f Z.matrix ξ := rfl

theorem literalCompleted_native (f : Adelic.FiniteSchwartz.finiteSchwartz F (3 * 1))
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Adelic.BallGeometryData.FrameIndex A₁)) (ξ : Adelic.BallGeometryData.FrameIndex A₁ → ℂ) :
    literalCompleted B₁.rationalPosition f Z ξ = Adelic.DataTheta.completedTheta B₁ f Z.matrix ξ := rfl

theorem theta_blocks (hΘ₁ : Adelic.DataTheta.Descent.ThetaConstruction B₁) (hΘ₂ : Adelic.DataTheta.Descent.ThetaConstruction B₂)
    (f₁ : Adelic.FiniteSchwartz.finiteSchwartz F 3) (f₂ : Adelic.FiniteSchwartz.finiteSchwartz F 3)
    (Z₁ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Adelic.BallGeometryData.FrameIndex A₁)) (Z₂ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Adelic.BallGeometryData.FrameIndex A₂))
    (ξ₁ : Adelic.BallGeometryData.FrameIndex A₁ → ℂ) (ξ₂ : Adelic.BallGeometryData.FrameIndex A₂ → ℂ) :
    literalTheta (blockPosition B₁.rationalPosition B₂.rationalPosition)
      (IntrinsicSchwartz.Intrinsic.productInput F 3 3 f₁ f₂) (IntrinsicBlockSiegel.Intrinsic.blockPeriod Z₁ Z₂).matrix (Sum.elim ξ₁ ξ₂) =
      Adelic.DataTheta.rationalTheta B₁ f₁ Z₁.matrix ξ₁ * Adelic.DataTheta.rationalTheta B₂ f₂ Z₂.matrix ξ₂ := by
  unfold literalTheta
  rw [← (positionSplit F).symm.toEquiv.tsum_eq]
  have hterm (p : (Fin 3 → F) × (Fin 3 → F)) :
      Adelic.Evaluation.finiteSchwartzFunction F 6 (IntrinsicSchwartz.Intrinsic.productInput F 3 3 f₁ f₂)
        (fun i => algebraMap F (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles F) ((positionSplit F).symm p i)) *
        kernel (IntrinsicBlockSiegel.Intrinsic.blockPeriod Z₁ Z₂).matrix (Sum.elim ξ₁ ξ₂)
          (fun i => (blockPosition B₁.rationalPosition B₂.rationalPosition
            ((positionSplit F).symm p) i : ℝ)) =
      Adelic.DataTheta.thetaSummand B₁ f₁ Z₁.matrix ξ₁ p.1 * Adelic.DataTheta.thetaSummand B₂ f₂ Z₂.matrix ξ₂ p.2 := by
    have hp₁ (i : Fin 3) : (positionSplit F).symm p (Fin.castAdd 3 i) = p.1 i := by
      exact congrArg (fun q : (Fin 3 → F) × (Fin 3 → F) => q.1 i)
        ((positionSplit F).apply_symm_apply p)
    have hp₂ (i : Fin 3) : (positionSplit F).symm p (Fin.natAdd 3 i) = p.2 i := by
      exact congrArg (fun q : (Fin 3 → F) × (Fin 3 → F) => q.2 i)
        ((positionSplit F).apply_symm_apply p)
    have hR : (fun i => (blockPosition B₁.rationalPosition B₂.rationalPosition
        ((positionSplit F).symm p) i : ℝ)) =
        Sum.elim (fun i => (B₁.rationalPosition p.1 i : ℝ))
          (fun i => (B₂.rationalPosition p.2 i : ℝ)) := by
      simp only [blockPosition, LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
        LinearEquiv.apply_symm_apply, LinearEquiv.prodCongr_apply]
      funext i
      rcases i with i | i <;> rfl
    rw [IntrinsicSchwartz.Intrinsic.productInput_value F 3 3 f₁ f₂, hR, kernel_blocks]
    simp only [hp₁, hp₂, Adelic.DataTheta.thetaSummand, Adelic.DataTheta.rationalWeight, Adelic.DataTheta.gaussianValue, kernel]
    ring
  calc
    _ = ∑' p : (Fin 3 → F) × (Fin 3 → F),
        Adelic.DataTheta.thetaSummand B₁ f₁ Z₁.matrix ξ₁ p.1 * Adelic.DataTheta.thetaSummand B₂ f₂ Z₂.matrix ξ₂ p.2 :=
      tsum_congr hterm
    _ = _ := (tsum_mul_tsum_of_summable_norm (hΘ₁.2.1 f₁ Z₁ ξ₁).norm
      (hΘ₂.2.1 f₂ Z₂ ξ₂).norm).symm

end RepresentationTheory.Theta.Kernel.IntrinsicBlockCompletion.IntrinsicKernel

namespace RepresentationTheory.Theta.Kernel.IntrinsicBlockCompletion.Intrinsic

/-! The quadratic completion factors in the constructed block period,
so the literal native completed theta kernel factors as well. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise
open _root_.Matrix

open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSchwartz.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicBlockSiegel.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicBlockCompletion.IntrinsicKernel

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem completion_blocks (Z₁ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (Z₂ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix J)
    (ξ₁ : I → ℂ) (ξ₂ : J → ℂ) :
    AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor (((Real.pi : ℂ) / 2) •
      AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear ((AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary (IntrinsicBlockSiegel.Intrinsic.blockPeriod Z₁ Z₂).matrix)⁻¹))
      (Sum.elim ξ₁ ξ₂) =
    AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor (((Real.pi : ℂ) / 2) •
      AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear ((AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary Z₁.matrix)⁻¹)) ξ₁ *
    AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor (((Real.pi : ℂ) / 2) •
      AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear ((AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary Z₂.matrix)⁻¹)) ξ₂ := by
  have hIm : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary (IntrinsicBlockSiegel.Intrinsic.blockPeriod Z₁ Z₂).matrix =
      fromBlocks (AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary Z₁.matrix) 0 0 (AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary Z₂.matrix) := by
    funext i j
    rcases i with i | i <;> rcases j with j | j <;> rfl
  have hinv : (AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary (IntrinsicBlockSiegel.Intrinsic.blockPeriod Z₁ Z₂).matrix)⁻¹ =
      fromBlocks (AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary Z₁.matrix)⁻¹ 0 0 (AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary Z₂.matrix)⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [hIm, fromBlocks_multiply]
    simp only [Matrix.mul_nonsing_inv _ Z₁.matrixImaginary_det_isUnit,
      Matrix.mul_nonsing_inv _ Z₂.matrixImaginary_det_isUnit,
      Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero, fromBlocks_one]
  simp only [AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor, _root_.smul_apply, smul_eq_mul,
    AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear_apply, hinv, dotProduct, Matrix.mulVec, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul,
    Finset.sum_const_zero, zero_add, add_zero]
  rw [← Complex.exp_add]
  congr 1
  ring

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ K₂ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A₁ : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁} {A₂ : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₂}
variable (B₁ : Adelic.DataTheta.ComparisonData F H K₁ A₁) (B₂ : Adelic.DataTheta.ComparisonData F H K₂ A₂)

theorem completed_blocks (hΘ₁ : Adelic.DataTheta.Descent.ThetaConstruction B₁) (hΘ₂ : Adelic.DataTheta.Descent.ThetaConstruction B₂)
    (f₁ : Adelic.FiniteSchwartz.finiteSchwartz F 3) (f₂ : Adelic.FiniteSchwartz.finiteSchwartz F 3)
    (Z₁ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Adelic.BallGeometryData.FrameIndex A₁)) (Z₂ : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Adelic.BallGeometryData.FrameIndex A₂))
    (ξ₁ : Adelic.BallGeometryData.FrameIndex A₁ → ℂ) (ξ₂ : Adelic.BallGeometryData.FrameIndex A₂ → ℂ) :
    IntrinsicKernel.literalCompleted (IntrinsicKernel.blockPosition B₁.rationalPosition B₂.rationalPosition)
      (IntrinsicSchwartz.Intrinsic.productInput F 3 3 f₁ f₂) (IntrinsicBlockSiegel.Intrinsic.blockPeriod Z₁ Z₂) (Sum.elim ξ₁ ξ₂) =
      Adelic.DataTheta.completedTheta B₁ f₁ Z₁.matrix ξ₁ * Adelic.DataTheta.completedTheta B₂ f₂ Z₂.matrix ξ₂ := by
  unfold IntrinsicKernel.literalCompleted
  rw [completion_blocks, IntrinsicKernel.theta_blocks B₁ B₂ hΘ₁ hΘ₂]
  unfold Adelic.DataTheta.completedTheta
  ring

end RepresentationTheory.Theta.Kernel.IntrinsicBlockCompletion.Intrinsic

end

end OAI
