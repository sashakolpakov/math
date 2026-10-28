import OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionMatrices
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicInversePullback

/-! # Intrinsic Imaginary Comparison -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicImaginaryComparison.Intrinsic

noncomputable section

/-! Native inverse-imaginary transport for the completed theta kernels.
The real symplectic comparison determines the imaginary bilinear form. -/

open scoped _root_.NumberField Classical _root_.Matrix BigOperators _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicGlobal OAI.RepresentationTheory.Theta.Kernel.IntrinsicBlockSiegel.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicRealTransport.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicComplexTransport.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCoordinateAgreement.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSymplecticComparison.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCoordinateAgreement.IntrinsicPositionTransport OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionMatrices.IntrinsicShearComparison
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionMatrices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicInversePullback.Intrinsic

abbrev realImaginary {I : Type} (Z : Matrix I I ℂ) : Matrix I I ℝ := Z.map Complex.im

theorem cross_graph_difference {k I J : Type} [Field k] [Fintype I] [Fintype J]
    (E : ((I ⊕ I) → k) →ₗ[k] ((J ⊕ J) → k)) (R : (I → k) →ₗ[k] (J → k))
    (Z : Matrix I I k) (W : Matrix J J k)
    (hpair : ∀ x y, Adelic.DataTheta.standardPairing (E x) (E y) = Adelic.DataTheta.standardPairing x y)
    (hpos : ∀ x, IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions k J (E x) = R (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions k I x))
    (hgraph : ∀ x, E (Sum.elim x (Z.mulVec x)) = Sum.elim (R x) (W.mulVec (R x)))
    (x y : I → k) :
    (∑ j, R x j * W.mulVec (R y) j) - (∑ i, x i * Z.mulVec y i) =
      ∑ j, E (Sum.elim x (0 : I → k)) (.inr j) * R y j := by
  have h := hpair (Sum.elim x (0 : I → k)) (Sum.elim y (Z.mulVec y))
  rw [hgraph] at h
  have hp (j : J) : E (Sum.elim x (0 : I → k)) (.inl j) = R x j :=
    congrFun (hpos (Sum.elim x (0 : I → k))) j
  simp only [Adelic.DataTheta.standardPairing, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_mul, sub_zero] at h
  simp_rw [hp] at h
  rw [Finset.sum_sub_distrib] at h
  linear_combination h

theorem complex_bilinear_im {I : Type} [Fintype I]
    (Z : Matrix I I ℂ) (x y : I → ℝ) :
    (∑ i, (x i : ℂ) * Z.mulVec (fun j => (y j : ℂ)) i).im =
      x ⬝ᵥ ((realImaginary Z).mulVec y) := by
  simp [Matrix.mulVec, dotProduct, Complex.mul_im]

theorem congruence_of_bilinear {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (R : Matrix J I ℝ) (X : Matrix I I ℝ) (Y : Matrix J J ℝ)
    (h : ∀ x y, (R.mulVec x) ⬝ᵥ (Y.mulVec (R.mulVec y)) = x ⬝ᵥ (X.mulVec y)) :
    Rᵀ * Y * R = X := by
  have he (x y : I → ℝ) : x ⬝ᵥ ((Rᵀ * Y * R).mulVec y) = x ⬝ᵥ (X.mulVec y) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec,
      dotProduct_comm]
    exact h x y
  ext i j
  simpa using he (Pi.single i 1) (Pi.single j 1)

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁} {S : IntrinsicSplitting.IntrinsicSummands.SecondLine A}
variable {P₁ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K₁} {P₂ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H S.form}
variable (B₁ : Adelic.DataTheta.ComparisonData F H K₁ A)
variable (B₂ : Adelic.DataTheta.ComparisonData F H S.form (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))
variable (B : Adelic.DataTheta.ComparisonData F H (IntrinsicSplitting.IntrinsicArithmetic.blockUnit K₁ S.form) (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S))

theorem real_imaginary_bilinear
    (hC₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁) (hC₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂)
    (hC : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (hG₁ : Adelic.DataTheta.GeometryIdentification B₁) (hG₂ : Adelic.DataTheta.GeometryIdentification B₂)
    (hG : Adelic.DataTheta.GeometryIdentification B) (z : Adelic.BallNatural.Ball) (x y : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℝ) :
    ((IntrinsicPositionMatrices.Intrinsic.realPositionMatrix B₁ B₂ B).mulVec x) ⬝ᵥ
        ((realImaginary (IntrinsicBlockSiegel.Intrinsic.blockPeriod (B₁.period z) (B₂.period z)).matrix).mulVec
          ((IntrinsicPositionMatrices.Intrinsic.realPositionMatrix B₁ B₂ B).mulVec y)) =
      x ⬝ᵥ ((realImaginary (B.period z).matrix).mulVec y) := by
  have hr (t : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℝ) :
      IntrinsicCoordinateAgreement.IntrinsicPositionTransport.complexPositionChange B₁ B₂ B (fun i => (t i : ℂ)) =
        fun i => ((IntrinsicPositionMatrices.Intrinsic.realPositionMatrix B₁ B₂ B).mulVec t i : ℂ) :=
    (IntrinsicPositionMatrices.Intrinsic.positionMatrix_apply B₁ B₂ B hC₁ hC₂ hC _).symm.trans (IntrinsicPositionMatrices.Intrinsic.positionMatrix_ofReal B₁ B₂ B t)
  have h := cross_graph_difference (IntrinsicComplexTransport.Intrinsic.complexPhaseChange B₁ B₂ B).toLinearMap
    (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.complexPositionChange B₁ B₂ B) (B.period z).matrix
    (IntrinsicBlockSiegel.Intrinsic.blockPeriod (B₁.period z) (B₂.period z)).matrix
    (IntrinsicSymplecticComparison.Intrinsic.complexPhaseChange_pairing B₁ B₂ B hC₁ hC₂ hC)
    (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.complexPhaseChange_positions B₁ B₂ B hC₁ hC₂ hC)
    (IntrinsicPositionMatrices.IntrinsicShearComparison.graph_in_positions B₁ B₂ B hC₁ hC₂ hC hG₁ hG₂ hG z)
      (fun i => (x i : ℂ)) (fun i => (y i : ℂ))
  rw [hr x, hr y] at h
  have he := IntrinsicCoordinateAgreement.Intrinsic.complexPhaseChange_real B₁ B₂ B hC₁ hC₂ hC
    (Sum.elim x (0 : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℝ))
  have hc : (fun i => ((Sum.elim x (0 : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℝ)) i : ℂ)) =
      Sum.elim (fun i => (x i : ℂ)) (0 : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ) := by
    funext i
    cases i <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, Complex.ofReal_zero]
  rw [hc] at he
  change _ - _ = ∑ j, IntrinsicComplexTransport.Intrinsic.complexPhaseChange B₁ B₂ B
      (Sum.elim (fun i => (x i : ℂ)) (0 : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ)) (.inr j) *
        ((IntrinsicPositionMatrices.Intrinsic.realPositionMatrix B₁ B₂ B).mulVec y j : ℂ) at h
  rw [he] at h
  have hi := congrArg Complex.im h
  rw [Complex.sub_im, complex_bilinear_im, complex_bilinear_im] at hi
  have hz : (∑ j,
      (IntrinsicRealTransport.Intrinsic.realPhaseChange B₁ B₂ B (Sum.elim x (0 : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℝ)) (.inr j) : ℂ) *
        ((IntrinsicPositionMatrices.Intrinsic.realPositionMatrix B₁ B₂ B).mulVec y j : ℂ)).im = 0 := by simp
  rw [hz] at hi
  exact sub_eq_zero.mp hi

theorem imaginary_congruence
    (hC₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁) (hC₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂)
    (hC : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (hG₁ : Adelic.DataTheta.GeometryIdentification B₁) (hG₂ : Adelic.DataTheta.GeometryIdentification B₂)
    (hG : Adelic.DataTheta.GeometryIdentification B) (z : Adelic.BallNatural.Ball) :
    (IntrinsicPositionMatrices.Intrinsic.positionMatrix B₁ B₂ B)ᵀ *
      AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary (IntrinsicBlockSiegel.Intrinsic.blockPeriod (B₁.period z) (B₂.period z)).matrix * IntrinsicPositionMatrices.Intrinsic.positionMatrix B₁ B₂ B =
        AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary (B.period z).matrix := by
  have h := congruence_of_bilinear (IntrinsicPositionMatrices.Intrinsic.realPositionMatrix B₁ B₂ B)
    (realImaginary (B.period z).matrix)
    (realImaginary (IntrinsicBlockSiegel.Intrinsic.blockPeriod (B₁.period z) (B₂.period z)).matrix)
    (real_imaginary_bilinear B₁ B₂ B hC₁ hC₂ hC hG₁ hG₂ hG z)
  have hc := congrArg (fun M => M.map Complex.ofRealHom) h
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map] at hc
  simp only [← IntrinsicPositionMatrices.Intrinsic.positionMatrix_real] at hc
  exact hc

theorem imaginary_inverse
    (hC₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁) (hC₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂)
    (hC : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (hG₁ : Adelic.DataTheta.GeometryIdentification B₁) (hG₂ : Adelic.DataTheta.GeometryIdentification B₂)
    (hG : Adelic.DataTheta.GeometryIdentification B) (z : Adelic.BallNatural.Ball) :
    (AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary (IntrinsicBlockSiegel.Intrinsic.blockPeriod (B₁.period z) (B₂.period z)).matrix)⁻¹ =
      IntrinsicPositionMatrices.Intrinsic.positionMatrix B₁ B₂ B * (AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary (B.period z).matrix)⁻¹ * (IntrinsicPositionMatrices.Intrinsic.positionMatrix B₁ B₂ B)ᵀ :=
  IntrinsicInversePullback.Intrinsic.inverse_congruence _ (IntrinsicPositionMatrices.Intrinsic.positionInverse B₁ B₂ B) _ _ (IntrinsicPositionMatrices.Intrinsic.positionMatrix_inverse B₁ B₂ B)
    (B.period z).matrixImaginary_det_isUnit
    (IntrinsicBlockSiegel.Intrinsic.blockPeriod (B₁.period z) (B₂.period z)).matrixImaginary_det_isUnit
    (imaginary_congruence B₁ B₂ B hC₁ hC₂ hC hG₁ hG₂ hG z)

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicImaginaryComparison.Intrinsic
