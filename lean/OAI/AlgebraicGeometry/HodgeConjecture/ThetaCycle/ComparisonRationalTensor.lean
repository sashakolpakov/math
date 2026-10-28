import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicTensorComplexCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicCoordinates

/-! # Comparison Rational Tensor -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ComparisonRationalTensor.CM

noncomputable section

/-! Rational and complex tensor identifications for every comparison
witness satisfying the full native coordinate proposition. These lemmas
do not require a particular choice of native comparison coordinates. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W) (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H W)
  (C : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData F H W A) (hC : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification C P)

include hC in
theorem comparison_complex_phase_rational_tensor (x : RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d 3 m) :
    C.complexPhase (fun i => (C.rationalPhase (P.rational.coordinates x) i : ℂ)) =
      RepresentationTheory.Theta.Adelic.BallGeometryData.realTensorComponents A (fun v j => RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d (.inl (A.enumerate v)) (x j)) := by
  have h := hC.2.2.2.2.2.2.1
    (fun v j => RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d (.inl (A.enumerate v)) (x j))
  have he :
      (fun v j => A.real v ((P.localFrame (.inl (A.enumerate v))).coordinates
        (fun j => RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal F d (.inl (A.enumerate v)) (x j)) j)) =
      (fun v j => A.real v (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) (P.rational.coordinates x j))) := by
    funext v j
    rw [P.coordinates_compatible]
  rw [he] at h
  have hc : (fun i => (C.realPhase
      (fun v j => A.real v (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) (P.rational.coordinates x j))) i : ℂ)) =
      (fun i => (C.rationalPhase (P.rational.coordinates x) i : ℂ)) := by
    funext i
    rw [hC.2.2.2.1]
    norm_cast
  exact (congrArg C.complexPhase hc).symm.trans h

def comparisonTensorCoordinates : RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d 3 m ≃ₗ[ℚ] ((RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A ⊕ RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) → ℚ) :=
  ((P.rational.coordinates.restrictScalars ℚ).trans C.rationalPhase).trans (IntrinsicCoordinates.CM.nativePhaseSwapEquiv (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) ℚ)

include hC in
theorem comparison_tensor_coordinates_pairing (x y : RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d 3 m) :
    RepresentationTheory.Theta.Adelic.DataTheta.standardPairing (comparisonTensorCoordinates A P C x) (comparisonTensorCoordinates A P C y) =
      -Algebra.trace ℚ F (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.tracePairing d 3 m H.val W.val x y) := by
  change RepresentationTheory.Theta.Adelic.DataTheta.standardPairing (RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (C.rationalPhase (P.rational.coordinates x)))
    (RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (C.rationalPhase (P.rational.coordinates y))) = _
  rw [IntrinsicCoordinates.CM.native_standard_pairing_swap, hC.2.2.1, P.rational.preserves]

include hC in
theorem comparison_tensor_coordinates_pairing_eq
    (D : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData F H W A) (hD : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification D P)
    (x y : RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition d 3 m) :
    RepresentationTheory.Theta.Adelic.DataTheta.standardPairing (comparisonTensorCoordinates A P C x) (comparisonTensorCoordinates A P C y) =
      RepresentationTheory.Theta.Adelic.DataTheta.standardPairing (comparisonTensorCoordinates A P D x) (comparisonTensorCoordinates A P D y) :=
  (comparison_tensor_coordinates_pairing A P C hC x y).trans
    (comparison_tensor_coordinates_pairing A P D hD x y).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ComparisonRationalTensor.CM
