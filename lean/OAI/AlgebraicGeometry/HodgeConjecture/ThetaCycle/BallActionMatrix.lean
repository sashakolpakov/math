import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource
import OAI.RepresentationTheory.Weil.AdelicSplitting.TensorSpace

/-! # Ball Action Matrix -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallActionMatrix.CM

noncomputable section

/-! ThetaCycle: the actual rational principal action preserves the complex
Hermitian form after extending scalars. -/

open scoped Classical
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]

def ballActionMatrix (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) : Matrix (Fin 3) (Fin 3) ℂ :=
  (LinearMap.toMatrix' g.toLinearMap).map K.subtype

def ballHermitianMatrix (B : HeckeCycles.GeometricSource.CM.BallDatum K) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal (fun j => if j = 2 then (B.b : ℂ) else 1)

theorem ball_action_matrix_unitary (B : HeckeCycles.GeometricSource.CM.BallDatum K) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K)
    (hg : ∀ x y, HeckeCycles.GeometricSource.CM.hermitian K B.b (g x) (g y) = HeckeCycles.GeometricSource.CM.hermitian K B.b x y) :
    (ballActionMatrix K g).conjTranspose * ballHermitianMatrix K B * ballActionMatrix K g =
      ballHermitianMatrix K B := by
  ext i j
  have hs : HeckeCycles.GeometricSource.CM.hermitian K B.b (Pi.single j 1) (Pi.single i 1) =
      if i = j then (if i = 2 then B.b else 1) else 0 := by
    simp [HeckeCycles.GeometricSource.CM.hermitian, Pi.single_apply, eq_comm]
  have hc (x : K) : K.subtype (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K x) = star (K.subtype x) := ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_coe K x
  have h := congrArg K.subtype (hg (Pi.single j 1) (Pi.single i 1))
  rw [hs] at h
  simp only [HeckeCycles.GeometricSource.CM.hermitian, map_sum, map_mul, hc, apply_ite K.subtype, map_one, map_zero] at h
  simp only [show K.subtype B.b = (B.b : ℂ) from rfl] at h
  change (∑ k, ((ballActionMatrix K g).conjTranspose * ballHermitianMatrix K B) i k *
    ballActionMatrix K g k j) = _
  simp only [ballHermitianMatrix, Matrix.mul_diagonal, ballActionMatrix,
    Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.diagonal_apply,
    LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
  convert h using 1
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem ball_hermitian_real (B : HeckeCycles.GeometricSource.CM.BallDatum K) (x : HeckeCycles.GeometricSource.CM.Vec ℂ) :
    (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue (ballHermitianMatrix K B) x x).re =
      Complex.normSq (x 0) + Complex.normSq (x 1) + (B.b : ℂ).re * Complex.normSq (x 2) := by
  simp [RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue, ballHermitianMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

theorem ball_action_preserves_real_form (B : HeckeCycles.GeometricSource.CM.BallDatum K) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K)
    (hg : ∀ x y, HeckeCycles.GeometricSource.CM.hermitian K B.b (g x) (g y) = HeckeCycles.GeometricSource.CM.hermitian K B.b x y) (x : HeckeCycles.GeometricSource.CM.Vec ℂ) :
    let y := (ballActionMatrix K g).mulVec x
    Complex.normSq (y 0) + Complex.normSq (y 1) + (B.b : ℂ).re * Complex.normSq (y 2) =
      Complex.normSq (x 0) + Complex.normSq (x 1) + (B.b : ℂ).re * Complex.normSq (x 2) := by
  dsimp only
  rw [← ball_hermitian_real K B, ← ball_hermitian_real K B,
    RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.formValue_change,
    ball_action_matrix_unitary K B g hg, ball_hermitian_real]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallActionMatrix.CM
