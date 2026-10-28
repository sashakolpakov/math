import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineArithmetic
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.QuadraticMultiplicityBasis

/-! # Single Line Trace -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineTrace.CM

noncomputable section

/-! Exact rational trace coordinates for one source multiplicity line.
The native phase swap retains the original positive source trace form. -/

open scoped Classical _root_.NumberField _root_.Matrix Kronecker
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.PhaseCoordinates

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  (δ : K) (hδ : IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)

def singleLineQuadraticPosition (x : HeckeCycles.GeometricSource.CM.Vec K) : RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (QuadraticModel.CM.cmQuadraticParameter K δ hδ) 3 1 :=
  fun ij => (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm (x ij.1)

def directSingleLineTensorEquiv : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[ℚ] RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (QuadraticModel.CM.cmQuadraticParameter K δ hδ) 3 1 where
  toFun := singleLineQuadraticPosition K δ hδ hδ0
  invFun y i := QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0 (y (i, 0))
  left_inv x := by funext i; exact (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).apply_symm_apply _
  right_inv y := by
    funext ij
    change (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0 (y (ij.1, 0))) = y ij
    rw [AlgEquiv.symm_apply_apply]
    exact congrArg (fun j => y (ij.1, j)) (Subsingleton.elim 0 ij.2)
  map_add' x y := by funext i; exact map_add (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm _ _
  map_smul' c x := by
    funext i
    exact ((QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm.toLinearEquiv.restrictScalars ℚ).map_smul c (x i.1)

variable (a : K) (ha : IsCMField.complexConj K a = a) (ha0 : a ≠ 0)
  (β : K) (hβ : IsCMField.complexConj K β = β) (hβ0 : β ≠ 0)

theorem direct_single_line_skew_unit_diagonal :
    (SingleLineArithmetic.CM.directSingleLineSkewUnit K δ hδ hδ0 a ha ha0).val =
      Matrix.diagonal (fun _ : Fin 1 => (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm (2 * δ * a)) := by
  apply Matrix.ext
  intro i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i j
  exact congrArg (fun M : Matrix (Fin 2) (Fin 2) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (maximalRealSubfield K)
    (QuadraticModel.CM.cmQuadraticParameter K δ hδ)) => M 0 0)
    (QuadraticMultiplicityBasis.CM.direct_source_skew_unit_diagonal K δ hδ hδ0 (fun _ => a) (fun _ => ha) (fun _ => ha0))

theorem direct_single_line_tensor_form (x y : HeckeCycles.GeometricSource.CM.Vec K) :
    RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue ((CMGlobalFrames.CM.cmHermitianUnit K δ hδ β hβ hβ0).val ⊗ₖ (SingleLineArithmetic.CM.directSingleLineSkewUnit K δ hδ hδ0 a ha ha0).val)
      (singleLineQuadraticPosition K δ hδ hδ0 x) (singleLineQuadraticPosition K δ hδ hδ0 y) =
      (-2 * (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm δ) *
        star ((QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm ((-a) * HeckeCycles.GeometricSource.CM.hermitian K β x y)) := by
  rw [← QuadraticModel.CM.cm_quadratic_equiv_conjugation]
  rw [CMGlobalFrames.CM.cm_hermitian_unit_val K δ hδ hδ0, direct_single_line_skew_unit_diagonal]
  apply (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).injective
  simp only [RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue, QuadraticTensor.CM.quadraticHermitianMatrix, Matrix.diagonal_kronecker_diagonal,
    Matrix.mulVec_diagonal, dotProduct, singleLineQuadraticPosition,
    ← QuadraticModel.CM.cm_quadratic_equiv_conjugation, map_sum, map_mul, map_neg, map_ofNat, AlgEquiv.apply_symm_apply]
  simp only [HeckeCycles.GeometricSource.CM.hermitian, map_sum, map_mul,
    ha, apply_ite, hβ, map_one, Fintype.sum_prod_type, Fin.sum_univ_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hc : IsCMField.complexConj K (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K (y i)) = y i :=
    IsCMField.complexConj_apply_apply K (y i)
  rw [hc]
  ring

theorem direct_single_line_tensor_trace (x y : HeckeCycles.GeometricSource.CM.Vec K) :
    Algebra.trace ℚ (maximalRealSubfield K)
      (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.tracePairing (QuadraticModel.CM.cmQuadraticParameter K δ hδ) 3 1 (CMGlobalFrames.CM.cmHermitianUnit K δ hδ β hβ hβ0).val
        (SingleLineArithmetic.CM.directSingleLineSkewUnit K δ hδ hδ0 a ha ha0).val
        (singleLineQuadraticPosition K δ hδ hδ0 x) (singleLineQuadraticPosition K δ hδ hδ0 y)) =
      -Algebra.trace ℚ K (δ * a * HeckeCycles.GeometricSource.CM.hermitian K β x y) := by
  have hd : star ((QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm δ) = -(QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm δ := by
    rw [← QuadraticModel.CM.cm_quadratic_equiv_conjugation, hδ, map_neg]
  rw [RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.tracePairing, direct_single_line_tensor_form K δ hδ hδ0 a ha ha0 β hβ hβ0,
    QuadraticModel.CM.quadratic_skew_trace_normalization _ _ _ hd, QuadraticModel.CM.cm_quadratic_rational_trace K δ hδ hδ0,
    map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  simp only [neg_mul, mul_neg, map_neg, mul_assoc]

variable (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ) 1
  (CMGlobalFrames.CM.cmHermitianUnit K δ hδ β hβ hβ0) (SingleLineArithmetic.CM.directSingleLineSkewUnit K δ hδ hδ0 a ha ha0))

def directSingleLineRationalCoordinates : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[ℚ] ((RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A ⊕ RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) → ℚ) :=
  (((directSingleLineTensorEquiv K δ hδ hδ0).trans
    ((SingleLineArithmetic.CM.directSingleLineGlobalFrames K δ hδ hδ0 a ha ha0 β hβ hβ0).rational.coordinates.restrictScalars ℚ)).trans
      (RepresentationTheory.Theta.Adelic.PhaseCoordinates.rationalPhaseCoordinates A)).trans (IntrinsicCoordinates.CM.nativePhaseSwapEquiv (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) ℚ)

theorem direct_single_line_rational_coordinates_pairing (x y : HeckeCycles.GeometricSource.CM.Vec K) :
    RepresentationTheory.Theta.Adelic.DataTheta.standardPairing (directSingleLineRationalCoordinates K δ hδ hδ0 a ha ha0 β hβ hβ0 A x)
      (directSingleLineRationalCoordinates K δ hδ hδ0 a ha ha0 β hβ hβ0 A y) =
      Algebra.trace ℚ K (δ * a * HeckeCycles.GeometricSource.CM.hermitian K β x y) := by
  change RepresentationTheory.Theta.Adelic.DataTheta.standardPairing (RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (RepresentationTheory.Theta.Adelic.PhaseCoordinates.rationalPhaseCoordinates A _)) (RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (RepresentationTheory.Theta.Adelic.PhaseCoordinates.rationalPhaseCoordinates A _)) = _
  rw [IntrinsicCoordinates.CM.native_standard_pairing_swap, RepresentationTheory.Theta.Adelic.PhaseCoordinates.rationalPhaseCoordinates_pairing]
  change -Algebra.trace ℚ (maximalRealSubfield K) (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing 3 1
    ((SingleLineArithmetic.CM.directSingleLineGlobalFrames K δ hδ hδ0 a ha ha0 β hβ hβ0).rational.coordinates
      (singleLineQuadraticPosition K δ hδ hδ0 x))
    ((SingleLineArithmetic.CM.directSingleLineGlobalFrames K δ hδ hδ0 a ha ha0 β hβ hβ0).rational.coordinates
      (singleLineQuadraticPosition K δ hδ hδ0 y))) = _
  rw [(SingleLineArithmetic.CM.directSingleLineGlobalFrames K δ hδ hδ0 a ha ha0 β hβ hβ0).rational.preserves,
    direct_single_line_tensor_trace, neg_neg]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineTrace.CM
