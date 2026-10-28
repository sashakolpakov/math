import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TwoFormWedge
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealCoordinateMeasure
import OAI.Analysis.HodgeTheory.Wedge
import OAI.AlgebraicTopology.Kunneth.WedgeAlgebra

/-! # Mixed Top Wedge -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.MixedTopWedge.CM

noncomputable section

/-! ThetaCycle: the native wedge of a holomorphic surface top covector and
the conjugate of another has its literal coefficient in real coordinates. -/

open OAI.AlgebraicTopology.Kunneth.WedgeAlgebra.Constructions OAI.Analysis.HodgeTheory.Wedge.Constructions.PolarizedPairing
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open scoped _root_.Matrix

def ballConjugateArea : Analysis.DifferentialForms.Manifold.Basic.FormValue HeckeCycles.GeometricSource.CM.BallChart 2 :=
  Complex.conjCLE.toContinuousLinearMap.compContinuousAlternatingMap PureTopCoefficient.CM.ballComplexArea

theorem ball_area_wedge_det (v : Fin 4 → HeckeCycles.GeometricSource.CM.BallChart) :
    AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge PureTopCoefficient.CM.ballComplexArea ballConjugateArea v =
      Matrix.det (fun i j => Fin.addCases (fun k : Fin 2 => v i k)
        (fun k : Fin 2 => star (v i k)) j) := by
  apply TwoFormWedge.CM.two_form_wedge_det PureTopCoefficient.CM.ballComplexArea ballConjugateArea
    (fun j x => x j) (fun j x => star (x j))
  · intro w
    rfl
  · intro w
    change star (Matrix.det w) = Matrix.det (fun i j => star (w i j))
    simpa only using! (RingHom.map_det (starRingEnd ℂ) (show Matrix (Fin 2) (Fin 2) ℂ from w))

def realBallCoordinateBasis : Fin 4 → HeckeCycles.GeometricSource.CM.BallChart :=
  ![![1, 0], ![0, 1], ![Complex.I, 0], ![0, Complex.I]]

theorem ball_area_wedge_real_basis :
    AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge PureTopCoefficient.CM.ballComplexArea ballConjugateArea realBallCoordinateBasis = -4 := by
  rw [ball_area_wedge_det]
  have hm : (fun i j => Fin.addCases (fun k : Fin 2 => realBallCoordinateBasis i k)
      (fun k : Fin 2 => star (realBallCoordinateBasis i k)) j) =
      (show Matrix (Fin 4) (Fin 4) ℂ from
        !![1, 0, 1, 0; 0, 1, 0, 1; Complex.I, 0, -Complex.I, 0; 0, Complex.I, 0, -Complex.I]) := by
    funext i j
    fin_cases i <;> fin_cases j <;> norm_num [realBallCoordinateBasis, Fin.addCases]
  rw [hm]
  let A : Matrix (Fin 4) (Fin 4) ℂ :=
    !![1, 0, 1, 0; 0, 1, 0, 1; Complex.I, 0, -Complex.I, 0; 0, Complex.I, 0, -Complex.I]
  have hb : A.submatrix (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4)
      (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4) = (Analysis.HodgeTheory.Wedge.Constructions.PolarizedPairing.canonicalWedgeMatrix 2).transpose := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      norm_num [A, Matrix.submatrix, finSumFinEquiv, Analysis.HodgeTheory.Wedge.Constructions.PolarizedPairing.canonicalWedgeMatrix,
        Matrix.fromBlocks, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply]
  have hd := Matrix.det_submatrix_equiv_self (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4) A
  rw [hb, Matrix.det_transpose, Analysis.HodgeTheory.Wedge.Constructions.PolarizedPairing.canonicalWedgeMatrix_det] at hd
  change A.det = -4
  rw [← hd]
  norm_num [mul_pow]

theorem real_ball_coordinate_basis_eq :
    (fun i : Fin 4 => (Topology.Euclidean.ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv 2).symm
      (Pi.basisFun ℝ (Fin 4) i)) = realBallCoordinateBasis := by
  funext i j
  rw [Topology.Euclidean.ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv_symm_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [realBallCoordinateBasis, Topology.Euclidean.ComplexModelRealCoordinates.Globalization.complexRealCoordinateIndexEquiv, Pi.basisFun_apply,
      finSumFinEquiv, Pi.single_apply, Fin.castAdd, Fin.addNat, Fin.castLE]

theorem mixed_pure_top_wedge_real_coefficient (a b : Analysis.DifferentialForms.Manifold.Basic.FormValue HeckeCycles.GeometricSource.CM.BallChart 2)
    (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree HeckeCycles.GeometricSource.CM.BallChart 2 0 a) (hb : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree HeckeCycles.GeometricSource.CM.BallChart 2 0 b) :
    AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge a (Complex.conjCLE.toContinuousLinearMap.compContinuousAlternatingMap b)
      (fun i : Fin 4 => (Topology.Euclidean.ComplexModelRealCoordinates.Globalization.complexModelRealContinuousLinearEquiv 2).symm
        (Pi.basisFun ℝ (Fin 4) i)) =
      -4 * (a (Pi.basisFun ℂ (Fin 2)) * star (b (Pi.basisFun ℂ (Fin 2)))) := by
  have hc : Complex.conjCLE.toContinuousLinearMap.compContinuousAlternatingMap b =
      star (b (Pi.basisFun ℂ (Fin 2))) • ballConjugateArea := by
    conv_lhs => rw [PureTopCoefficient.CM.pure_top_form_from_coefficient b hb]
    ext v
    change star (b (Pi.basisFun ℂ (Fin 2)) * PureTopCoefficient.CM.ballComplexArea v) =
      star (b (Pi.basisFun ℂ (Fin 2))) * star (PureTopCoefficient.CM.ballComplexArea v)
    exact map_mul (starRingEnd ℂ) _ _
  rw [hc]
  nth_rw 1 [PureTopCoefficient.CM.pure_top_form_from_coefficient a ha]
  rw [PureTopCoefficient.CM.ball_area_coefficient_apply, AlgebraicTopology.Kunneth.WedgeAlgebra.Constructions.covectorWedge_smul_left, AlgebraicTopology.Kunneth.WedgeAlgebra.Constructions.covectorWedge_smul_right]
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul,
    real_ball_coordinate_basis_eq, ball_area_wedge_real_basis]
  ring

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.MixedTopWedge.CM
