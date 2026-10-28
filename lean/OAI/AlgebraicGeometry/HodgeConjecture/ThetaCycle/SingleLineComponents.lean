import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineTrace
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceFrameComponents

/-! # Single Line Components -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineComponents.CM

noncomputable section

/-! The original CM components of one source line agree with the
corresponding column of the full native two-line model. -/

open scoped Classical _root_.NumberField _root_.Matrix Kronecker
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]

def singleSourcePairedCoordinates (places : HeckeCycles.GeometricSource.CM.Places K) :
    HeckeCycles.GeometricSource.CM.Ambient K →ₗ[ℂ] (Fin places.count → ((Fin 3 × Fin 1 → ℂ) × (Fin 3 × Fin 1 → ℂ))) where
  toFun w v := (fun ij => (Symplectic.CM.galoisToPaired K places w v).1 ij.1,
    fun ij => (Symplectic.CM.galoisToPaired K places w v).2 ij.1)
  map_add' x y := by
    funext v
    apply Prod.ext <;> funext ij <;> simp
  map_smul' c w := by
    funext v
    apply Prod.ext <;> funext ij <;> simp

variable {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Fin places.count → Bool}
  (Q : Lagrangians.CM.LagrangianPair K B places d) (hμ : ∀ j, d j places.distinguished = true) (j : Fin 2)

def directSingleLineFrames :
    RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K Q.delta Q.delta_imaginary) 3 1
      (CMGlobalFrames.CM.cmHermitianUnit K Q.delta Q.delta_imaginary B.b B.conjugate_b (BallArithmetic.CM.direct_source_ball_b_ne_zero K B))
      (SingleLineArithmetic.CM.directSingleLineSkewUnit K Q.delta Q.delta_imaginary Q.delta_ne_zero (Q.a j)
        (BallArithmetic.CM.direct_source_a_fixed K Q j) (BallArithmetic.CM.direct_source_a_ne_zero K Q j)) :=
  SingleLineArithmetic.CM.directSingleLineGlobalFrames K Q.delta Q.delta_imaginary Q.delta_ne_zero (Q.a j)
    (BallArithmetic.CM.direct_source_a_fixed K Q j) (BallArithmetic.CM.direct_source_a_ne_zero K Q j)
    B.b B.conjugate_b (BallArithmetic.CM.direct_source_ball_b_ne_zero K B)

abbrev directSingleLineComparison := RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) (directSingleLineFrames K Q j)

def directSingleLineComplexComponents : HeckeCycles.GeometricSource.CM.Ambient K →ₗ[ℂ] RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) :=
  (IntrinsicTensorComplexCoordinates.CM.nativePairedTensorComponents (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j)).comp (singleSourcePairedCoordinates K places)

theorem direct_single_line_normalizer_entry (v : Fin places.count) (i k : Fin 3) :
    IntrinsicTensorComplexCoordinates.CM.nativeTensorComponentNormalizer (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) v (i, 0) (k, 0) =
      IntrinsicTensorComplexCoordinates.CM.nativeTensorComponentNormalizer (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ B.other_place) v (i, j) (k, j) := by
  simp only [IntrinsicTensorComplexCoordinates.CM.nativeTensorComponentNormalizer, Matrix.kroneckerMap_apply]
  simp only [SingleLineArithmetic.CM.directSingleLineArithmetic, BallArithmetic.CM.directSourceBallArithmeticData,
    CMOrthonormalFrames.CM.singleLineSkewNormalizer, CMOrthonormalFrames.CM.sourceSkewNormalizer, DiagonalNormalization.CM.complexDiagonalNormalizer,
    DiagonalFrame.CM.diagonalMatrixUnit, Matrix.diagonal_apply_eq]
  rfl

theorem direct_single_line_tensor_normalizer (v : Fin places.count) :
    IntrinsicTensorComplexCoordinates.CM.nativeTensorComponentNormalizer (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) v =
      Matrix.diagonal (fun i : Fin 3 × Fin 1 => (SourceScales.CM.sourceNativeTensorScale K places Q.delta Q.a B.b v (i.1, j) : ℂ)) := by
  apply Matrix.ext
  rintro ⟨i, p⟩ ⟨k, q⟩
  fin_cases p
  fin_cases q
  have hn := direct_single_line_normalizer_entry K Q hμ j v i k
  have hd := congrArg (fun M : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ => M (i, j) (k, j))
    (SourceScales.CM.direct_source_tensor_normalizer K Q hμ B.other_place v)
  refine hn.trans ?_
  simpa only [Matrix.diagonal_apply, Prod.mk.injEq, and_true] using! hd

theorem direct_single_line_components_fst (w : HeckeCycles.GeometricSource.CM.Ambient K) (v : Fin places.count) (i : Fin 3 × Fin 1) :
    (directSingleLineComplexComponents K Q hμ j w v).1 i =
      (SourceScales.CM.sourceNativeTensorScale K places Q.delta Q.a B.b v (i.1, j) : ℂ) *
        (Symplectic.CM.galoisToPaired K places w v).1 i.1 := by
  change (IntrinsicTensorComplexCoordinates.CM.nativeTensorComponentNormalizer (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) v).mulVec
    (singleSourcePairedCoordinates K places w v).1 i = _
  rw [direct_single_line_tensor_normalizer, Matrix.mulVec_diagonal]
  rfl

theorem direct_single_line_components_snd (w : HeckeCycles.GeometricSource.CM.Ambient K) (v : Fin places.count) (i : Fin 3 × Fin 1) :
    (directSingleLineComplexComponents K Q hμ j w v).2 i =
      (if v = places.distinguished ∧ i.1 = 2 then (-1 : ℂ) else 1) *
        (if !(d j v) then (1 : ℂ) else -1) *
        ((SourceScales.CM.sourceNativeTensorScale K places Q.delta Q.a B.b v (i.1, j) : ℂ) *
          (Symplectic.CM.galoisToPaired K places w v).2 i.1) := by
  change _ * _ * ((IntrinsicTensorComplexCoordinates.CM.nativeTensorComponentNormalizer (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) v).map star).mulVec
    (singleSourcePairedCoordinates K places w v).2 i = _
  rw [direct_single_line_tensor_normalizer, Matrix.diagonal_map (star_zero _)]
  simp only [Matrix.mulVec_diagonal]
  rw [show star (SourceScales.CM.sourceNativeTensorScale K places Q.delta Q.a B.b v (i.1, j) : ℂ) =
    (SourceScales.CM.sourceNativeTensorScale K places Q.delta Q.a B.b v (i.1, j) : ℂ) from Complex.conj_ofReal _]
  rfl

theorem direct_single_line_components_projection (w : ComplexTransition.CM.TotalAmbient K) :
    directSingleLineComplexComponents K Q hμ j (w j) =
      fun v => (fun i : Fin 3 × Fin 1 => (SourceComponents.CM.directSourceComplexComponents K Q hμ B.other_place w v).1 (i.1, j),
        fun i : Fin 3 × Fin 1 => (SourceComponents.CM.directSourceComplexComponents K Q hμ B.other_place w v).2 (i.1, j)) := by
  refine funext (fun v : Fin places.count => ?_)
  apply Prod.ext
  · funext i
    exact (direct_single_line_components_fst K Q hμ j (w j) v i).trans
      (SourceFrameComponents.CM.direct_source_components_fst K Q hμ B.other_place w v (i.1, j)).symm
  · funext i
    exact (direct_single_line_components_snd K Q hμ j (w j) v i).trans
      (SourceFrameComponents.CM.direct_source_components_snd K Q hμ B.other_place w v (i.1, j)).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineComponents.CM
