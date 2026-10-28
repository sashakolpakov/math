import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSymplecticComparison
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCoordinateAgreement

/-! # Intrinsic Position Matrices -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Kernel.IntrinsicPositionMatrices.IntrinsicShearComparison

/-! The difference between the native total quadratic Gaussian and the
constructed block quadratic Gaussian is the rational shear of their
actual phase-coordinate change. -/

open scoped _root_.NumberField Classical _root_.Matrix BigOperators _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicGlobal OAI.RepresentationTheory.Theta.Kernel.IntrinsicHodgeSplit.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicBlockSiegel.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicBlockCompletion.IntrinsicKernel OAI.RepresentationTheory.Theta.Kernel.IntrinsicPhaseTransport.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicComplexTransport.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCoordinateAgreement.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCoordinateAgreement.IntrinsicPositionTransport OAI.RepresentationTheory.Theta.Kernel.IntrinsicSymplecticComparison.Intrinsic

def momenta (k I : Type) [Field k] : ((I ⊕ I) → k) →ₗ[k] (I → k) where
  toFun x i := x (.inr i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem quadratic_graph_difference {k I J : Type} [Field k] [Fintype I] [Fintype J]
    (E : ((I ⊕ I) → k) →ₗ[k] ((J ⊕ J) → k)) (R : (I → k) →ₗ[k] (J → k))
    (Z : Matrix I I k) (W : Matrix J J k)
    (hpair : ∀ x y, Adelic.DataTheta.standardPairing (E x) (E y) = Adelic.DataTheta.standardPairing x y)
    (hpos : ∀ x, IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions k J (E x) = R (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions k I x))
    (hgraph : ∀ x, E (Sum.elim x (Z.mulVec x)) = Sum.elim (R x) (W.mulVec (R x)))
    (x : I → k) :
    (∑ j, R x j * W.mulVec (R x) j) - (∑ i, x i * Z.mulVec x i) =
      ∑ j, E (Sum.elim x (0 : I → k)) (.inr j) * R x j := by
  have h := hpair (Sum.elim x (0 : I → k)) (Sum.elim x (Z.mulVec x))
  rw [hgraph] at h
  have hp (j : J) : E (Sum.elim x (0 : I → k)) (.inl j) = R x j :=
    congrFun (hpos (Sum.elim x (0 : I → k))) j
  simp only [Adelic.DataTheta.standardPairing, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_mul, sub_zero] at h
  simp_rw [hp] at h
  rw [Finset.sum_sub_distrib] at h
  linear_combination h

theorem siegelMatrixForm_as_dot {I : Type} [Fintype I]
    (Z : Matrix I I ℂ) (x : I → ℝ) :
    AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm Z x x = ∑ i, (x i : ℂ) * Z.mulVec (fun j => (x j : ℂ)) i := by
  simp only [AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁} {S : IntrinsicSplitting.IntrinsicSummands.SecondLine A}
variable {P₁ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K₁} {P₂ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H S.form}
variable (B₁ : Adelic.DataTheta.ComparisonData F H K₁ A)
variable (B₂ : Adelic.DataTheta.ComparisonData F H S.form (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))
variable (B : Adelic.DataTheta.ComparisonData F H (IntrinsicSplitting.IntrinsicArithmetic.blockUnit K₁ S.form) (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S))

def shearBilinear : (Fin 6 → F) →ₗ[ℚ] (Fin 6 → F) →ₗ[ℚ] ℚ :=
  (dotProductBilin ℚ ℚ).compl₁₂
    ((momenta ℚ _).comp ((IntrinsicPhaseTransport.Intrinsic.rationalPhaseChange B₁ B₂ B).toLinearMap.comp
      ((IntrinsicCoordinateAgreement.IntrinsicPositionTransport.embedPosition ℚ _).comp B.rationalPosition.toLinearMap)))
    (IntrinsicBlockCompletion.IntrinsicKernel.blockPosition B₁.rationalPosition B₂.rationalPosition).toLinearMap

theorem shearBilinear_apply (x y : Fin 6 → F) :
    shearBilinear B₁ B₂ B x y = ∑ j,
      IntrinsicPhaseTransport.Intrinsic.rationalPhaseChange B₁ B₂ B
        (Sum.elim (B.rationalPosition x) (0 : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℚ)) (.inr j) *
      IntrinsicBlockCompletion.IntrinsicKernel.blockPosition B₁.rationalPosition B₂.rationalPosition y j := rfl

theorem complexPositionChange_rational
    (hC₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁) (hC₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂)
    (hC : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (x : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℚ) :
    IntrinsicCoordinateAgreement.IntrinsicPositionTransport.complexPositionChange B₁ B₂ B (fun i => (x i : ℂ)) =
      fun i => (IntrinsicPhaseTransport.Intrinsic.rationalPositionChange B₁ B₂ B x i : ℂ) := by
  have h := IntrinsicCoordinateAgreement.Intrinsic.complexPhaseChange_rational B₁ B₂ B hC₁ hC₂ hC
    (Sum.elim x (0 : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℚ))
  have hc : (fun i => ((Sum.elim x (0 : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℚ)) i : ℂ)) =
      Sum.elim (fun i => (x i : ℂ)) (0 : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ) := by
    funext i
    cases i <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, Rat.cast_zero]
  rw [hc] at h
  ext i
  have hi := congrFun h (.inl i)
  rw [IntrinsicPhaseTransport.Intrinsic.rationalPhaseChange_position B₁ B₂ B hC₁ hC₂ hC] at hi
  exact hi

theorem graph_in_positions
    (hC₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁) (hC₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂)
    (hC : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (hG₁ : Adelic.DataTheta.GeometryIdentification B₁) (hG₂ : Adelic.DataTheta.GeometryIdentification B₂)
    (hG : Adelic.DataTheta.GeometryIdentification B) (z : Adelic.BallNatural.Ball) (x : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ) :
    IntrinsicComplexTransport.Intrinsic.complexPhaseChange B₁ B₂ B (Sum.elim x ((B.period z).matrix.mulVec x)) =
      Sum.elim (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.complexPositionChange B₁ B₂ B x)
        ((IntrinsicBlockSiegel.Intrinsic.blockPeriod (B₁.period z) (B₂.period z)).matrix.mulVec (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.complexPositionChange B₁ B₂ B x)) := by
  let a := (B.frame z).inv.mulVec x
  have ha : (B.frame z).val.mulVec a = x := by
    change (B.frame z).val.mulVec ((B.frame z).inv.mulVec x) = x
    rw [Matrix.mulVec_mulVec, (B.frame z).val_inv, Matrix.one_mulVec]
  have h := IntrinsicComplexTransport.Intrinsic.complexPhaseChange_graph B₁ B₂ B hG₁ hG₂ hG z a
  rw [ha] at h
  have hp := congrArg (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℂ _) h
  rw [IntrinsicCoordinateAgreement.IntrinsicPositionTransport.complexPhaseChange_positions B₁ B₂ B hC₁ hC₂ hC] at hp
  change IntrinsicCoordinateAgreement.IntrinsicPositionTransport.complexPositionChange B₁ B₂ B x =
    (IntrinsicBlockSiegel.Intrinsic.blockFrame (B₁.frame z) (B₂.frame z)).val.mulVec (IntrinsicHodgeSplit.Intrinsic.splitCoordinates A S a) at hp
  rw [← hp] at h
  exact h

theorem native_quadratic_difference
    (hC₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁) (hC₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂)
    (hC : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (hG₁ : Adelic.DataTheta.GeometryIdentification B₁) (hG₂ : Adelic.DataTheta.GeometryIdentification B₂)
    (hG : Adelic.DataTheta.GeometryIdentification B) (z : Adelic.BallNatural.Ball) (x : Fin 6 → F) :
    AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (IntrinsicBlockSiegel.Intrinsic.blockPeriod (B₁.period z) (B₂.period z)).matrix
        (fun i => (IntrinsicBlockCompletion.IntrinsicKernel.blockPosition B₁.rationalPosition B₂.rationalPosition x i : ℝ))
        (fun i => (IntrinsicBlockCompletion.IntrinsicKernel.blockPosition B₁.rationalPosition B₂.rationalPosition x i : ℝ)) -
      AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (B.period z).matrix
        (fun i => (B.rationalPosition x i : ℝ)) (fun i => (B.rationalPosition x i : ℝ)) =
      ((shearBilinear B₁ B₂ B x x : ℚ) : ℂ) := by
  let q := B.rationalPosition x
  have hr := complexPositionChange_rational B₁ B₂ B hC₁ hC₂ hC q
  have hq : IntrinsicPhaseTransport.Intrinsic.rationalPositionChange B₁ B₂ B q =
      IntrinsicBlockCompletion.IntrinsicKernel.blockPosition B₁.rationalPosition B₂.rationalPosition x := by
    change IntrinsicBlockCompletion.IntrinsicKernel.blockPosition B₁.rationalPosition B₂.rationalPosition (B.rationalPosition.symm (B.rationalPosition x)) = _
    rw [LinearEquiv.symm_apply_apply]
  rw [hq] at hr
  have h := quadratic_graph_difference (IntrinsicComplexTransport.Intrinsic.complexPhaseChange B₁ B₂ B).toLinearMap
    (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.complexPositionChange B₁ B₂ B) (B.period z).matrix
    (IntrinsicBlockSiegel.Intrinsic.blockPeriod (B₁.period z) (B₂.period z)).matrix
    (IntrinsicSymplecticComparison.Intrinsic.complexPhaseChange_pairing B₁ B₂ B hC₁ hC₂ hC)
    (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.complexPhaseChange_positions B₁ B₂ B hC₁ hC₂ hC)
    (graph_in_positions B₁ B₂ B hC₁ hC₂ hC hG₁ hG₂ hG z) (fun i => (q i : ℂ))
  rw [hr] at h
  have he := IntrinsicCoordinateAgreement.Intrinsic.complexPhaseChange_rational B₁ B₂ B hC₁ hC₂ hC
    (Sum.elim q (0 : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℚ))
  have hc : (fun i => ((Sum.elim q (0 : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℚ)) i : ℂ)) =
      Sum.elim (fun i => (q i : ℂ)) (0 : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ) := by
    funext i
    cases i <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, Rat.cast_zero]
  rw [hc] at he
  change _ - _ = ∑ j, IntrinsicComplexTransport.Intrinsic.complexPhaseChange B₁ B₂ B
    (Sum.elim (fun i => (q i : ℂ)) (0 : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ)) (.inr j) *
      (IntrinsicBlockCompletion.IntrinsicKernel.blockPosition B₁.rationalPosition B₂.rationalPosition x j : ℂ) at h
  rw [he] at h
  simpa only [siegelMatrixForm_as_dot, Complex.ofReal_ratCast,
    shearBilinear_apply, Rat.cast_sum, Rat.cast_mul] using h

end RepresentationTheory.Theta.Kernel.IntrinsicPositionMatrices.IntrinsicShearComparison

namespace RepresentationTheory.Theta.Kernel.IntrinsicPositionMatrices.Intrinsic

/-! Rational matrices of the native position change, their actual
inverses, and their real and complex scalar extensions. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicGlobal OAI.RepresentationTheory.Theta.Kernel.IntrinsicPhaseTransport.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCoordinateAgreement.IntrinsicPositionTransport OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionMatrices.IntrinsicShearComparison

def scalarMatrix {I J k : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Field k] [CharZero k] (e : (I → ℚ) ≃ₗ[ℚ] (J → ℚ)) : Matrix J I k :=
  (LinearMap.toMatrix' e.toLinearMap).map (Rat.castHom k)

theorem scalarMatrix_inverse {I J k : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Field k] [CharZero k]
    (e : (I → ℚ) ≃ₗ[ℚ] (J → ℚ)) :
    scalarMatrix (k := k) e * scalarMatrix (k := k) e.symm = (1 : Matrix J J k) := by
  have he : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact e.apply_symm_apply x
  unfold scalarMatrix
  rw [← Matrix.map_mul, ← LinearMap.toMatrix'_comp, he, LinearMap.toMatrix'_id, Matrix.map_one]
  all_goals simp

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁} {S : IntrinsicSplitting.IntrinsicSummands.SecondLine A}
variable {P₁ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K₁} {P₂ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H S.form}
variable (B₁ : Adelic.DataTheta.ComparisonData F H K₁ A)
variable (B₂ : Adelic.DataTheta.ComparisonData F H S.form (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))
variable (B : Adelic.DataTheta.ComparisonData F H (IntrinsicSplitting.IntrinsicArithmetic.blockUnit K₁ S.form) (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S))

def positionMatrix : Matrix (Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))
    (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S)) ℂ := scalarMatrix (IntrinsicPhaseTransport.Intrinsic.rationalPositionChange B₁ B₂ B)

def positionInverse : Matrix (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S))
    (Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)) ℂ :=
  scalarMatrix (IntrinsicPhaseTransport.Intrinsic.rationalPositionChange B₁ B₂ B).symm

def realPositionMatrix : Matrix (Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))
    (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S)) ℝ := scalarMatrix (IntrinsicPhaseTransport.Intrinsic.rationalPositionChange B₁ B₂ B)

theorem positionMatrix_inverse : positionMatrix B₁ B₂ B * positionInverse B₁ B₂ B = 1 :=
  scalarMatrix_inverse (IntrinsicPhaseTransport.Intrinsic.rationalPositionChange B₁ B₂ B)

theorem positionInverse_matrix : positionInverse B₁ B₂ B * positionMatrix B₁ B₂ B = 1 :=
  scalarMatrix_inverse (IntrinsicPhaseTransport.Intrinsic.rationalPositionChange B₁ B₂ B).symm

theorem positionMatrix_linear
    (hC₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁) (hC₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂)
    (hC : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂)) :
    Matrix.toLin' (positionMatrix B₁ B₂ B) = IntrinsicCoordinateAgreement.IntrinsicPositionTransport.complexPositionChange B₁ B₂ B := by
  apply LinearMap.toMatrix'.injective
  rw [LinearMap.toMatrix'_toLin']
  ext i j
  have h := IntrinsicShearComparison.complexPositionChange_rational B₁ B₂ B hC₁ hC₂ hC
    (Pi.single j (1 : ℚ))
  have hc : (fun k : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) =>
      ((Pi.single j (1 : ℚ) : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℚ) k : ℂ)) =
        (Pi.single j (1 : ℂ) : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ) := by
    funext k
    by_cases hk : k = j <;> simp [hk]
  rw [hc] at h
  exact (congrFun h i).symm

theorem positionMatrix_apply
    (hC₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁) (hC₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂)
    (hC : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (x : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ) :
    (positionMatrix B₁ B₂ B).mulVec x = IntrinsicCoordinateAgreement.IntrinsicPositionTransport.complexPositionChange B₁ B₂ B x :=
  congrArg (fun f => f x) (positionMatrix_linear B₁ B₂ B hC₁ hC₂ hC)

theorem positionMatrix_real :
    positionMatrix B₁ B₂ B = (realPositionMatrix B₁ B₂ B).map Complex.ofRealHom := by
  ext i j
  exact (Complex.ofReal_ratCast _).symm

theorem positionMatrix_ofReal (x : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℝ) :
    (positionMatrix B₁ B₂ B).mulVec (fun i => (x i : ℂ)) =
      fun i => ((realPositionMatrix B₁ B₂ B).mulVec x i : ℂ) := by
  rw [positionMatrix_real]
  funext i
  exact (RingHom.map_mulVec Complex.ofRealHom (realPositionMatrix B₁ B₂ B) x i).symm

end RepresentationTheory.Theta.Kernel.IntrinsicPositionMatrices.Intrinsic

end

end OAI
