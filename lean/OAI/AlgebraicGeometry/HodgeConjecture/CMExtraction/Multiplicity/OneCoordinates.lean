import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.MultiplicityOne
import OAI.RepresentationTheory.Theta.Adelic.DataTheta

/-! # One Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneCoordinates.Quadratic

noncomputable section

/-! The one-line AdelicTheta rational tensor coordinates, in the native
momentum/position order. The sign is computed from the actual trace form. -/

open scoped Classical _root_.NumberField
open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta

def phaseSwapEquiv (I : Type) (R : Type) [Field R] :
    ((I ⊕ I) → R) ≃ₗ[R] ((I ⊕ I) → R) where
  toFun := RepresentationTheory.Theta.Adelic.DataTheta.swapPhase
  invFun := RepresentationTheory.Theta.Adelic.DataTheta.swapPhase
  left_inv x := by funext i; cases i <;> rfl
  right_inv x := by funext i; cases i <;> rfl
  map_add' x y := by funext i; cases i <;> rfl
  map_smul' c x := by funext i; cases i <;> rfl

theorem standardPairing_swap {I R : Type} [Fintype I] [Field R]
    (x y : (I ⊕ I) → R) :
    RepresentationTheory.Theta.Adelic.DataTheta.standardPairing (RepresentationTheory.Theta.Adelic.DataTheta.swapPhase x) (RepresentationTheory.Theta.Adelic.DataTheta.swapPhase y) = -RepresentationTheory.Theta.Adelic.DataTheta.standardPairing x y := by
  simp only [RepresentationTheory.Theta.Adelic.DataTheta.standardPairing, RepresentationTheory.Theta.Adelic.DataTheta.swapPhase, Sum.elim_inl, Sum.elim_inr, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E]
  (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)

def singleTensorEquiv : (Fin 3 → E) ≃ₗ[ℚ] RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ) 3 1 where
  toFun := OneTrace.Quadratic.singleTensorPosition E δ hδ hδ0
  invFun y j := ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0 (y (j, 0))
  left_inv x := by funext j; exact (ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0).apply_symm_apply _
  right_inv y := by
    funext ⟨j, k⟩
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    exact (ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0).symm_apply_apply _
  map_add' x y := by funext i; exact map_add (ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0).symm _ _
  map_smul' c x := by
    funext i
    exact ((ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E δ hδ hδ0).symm.toLinearEquiv.restrictScalars ℚ).map_smul c (x i.1)

variable (b : E) (hb : IsCMField.complexConj E b = b) (hb0 : b ≠ 0)
  (a : E) (ha : IsCMField.complexConj E a = a) (ha0 : a ≠ 0)
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData (maximalRealSubfield E) (ThetaCycle.QuadraticModel.CM.cmQuadraticParameter E δ hδ) 1
    (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0) (MultiplicityOne.Quadratic.directSkewUnit E δ hδ hδ0 a ha ha0))
  (B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData (maximalRealSubfield E)
    (ThetaCycle.CMGlobalFrames.CM.cmHermitianUnit E δ hδ b hb hb0) (MultiplicityOne.Quadratic.directSkewUnit E δ hδ hδ0 a ha ha0) A)

def directRationalCoordinates : (Fin 3 → E) ≃ₗ[ℚ] ((RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A ⊕ RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) → ℚ) :=
  (((singleTensorEquiv E δ hδ hδ0).trans
    ((MultiplicityOne.Quadratic.directGlobalFrames E δ hδ hδ0 b hb hb0 a ha ha0).rational.coordinates.restrictScalars ℚ)).trans
      B.rationalPhase).trans (phaseSwapEquiv (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) ℚ)

theorem directRationalCoordinates_pairing
    (hCoord : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification B (MultiplicityOne.Quadratic.directGlobalFrames E δ hδ hδ0 b hb hb0 a ha ha0))
    (x y : Fin 3 → E) :
    RepresentationTheory.Theta.Adelic.DataTheta.standardPairing (directRationalCoordinates E δ hδ hδ0 b hb hb0 a ha ha0 A B x)
      (directRationalCoordinates E δ hδ hδ0 b hb hb0 a ha ha0 A B y) =
      Algebra.trace ℚ E (δ * (a * NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian b x y)) := by
  change RepresentationTheory.Theta.Adelic.DataTheta.standardPairing (RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (B.rationalPhase _)) (RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (B.rationalPhase _)) = _
  rw [standardPairing_swap, hCoord.2.2.1]
  change -Algebra.trace ℚ (maximalRealSubfield E)
    (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing 3 1
      ((MultiplicityOne.Quadratic.directGlobalFrames E δ hδ hδ0 b hb hb0 a ha ha0).rational.coordinates
        (OneTrace.Quadratic.singleTensorPosition E δ hδ hδ0 x))
      ((MultiplicityOne.Quadratic.directGlobalFrames E δ hδ hδ0 b hb hb0 a ha ha0).rational.coordinates
        (OneTrace.Quadratic.singleTensorPosition E δ hδ hδ0 y))) = _
  rw [(MultiplicityOne.Quadratic.directGlobalFrames E δ hδ hδ0 b hb hb0 a ha ha0).rational.preserves]
  rw [MultiplicityOne.Quadratic.direct_tensor_rational_trace, neg_neg]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneCoordinates.Quadratic
