import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CMOrthonormalFrames
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallActionMatrix
import OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

/-! # Rational Ball Unitary -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalBallUnitary.CM

noncomputable section

/-! ThetaCycle: identify the literal principal rational ball transformation
with an element of the native quadratic-algebra special-unitary group. -/

open scoped Classical _root_.NumberField
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

theorem matrix_unit_det_eq_one {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]
    (A : (Matrix I I R)ˣ) (h : A.val.det = 1) : Matrix.GeneralLinearGroup.det A = 1 :=
  Units.ext h

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]
  (δ : K) (hδ : IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)

def quadraticComplexEmbedding : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (maximalRealSubfield K)
    (QuadraticModel.CM.cmQuadraticParameter K δ hδ) →+* ℂ :=
  K.subtype.comp (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).toRingHom

theorem quadratic_complex_embedding_injective :
    Function.Injective (quadraticComplexEmbedding K δ hδ hδ0) :=
  K.subtype_injective.comp (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).injective

theorem quadratic_complex_embedding_star (x : RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (maximalRealSubfield K)
    (QuadraticModel.CM.cmQuadraticParameter K δ hδ)) :
    quadraticComplexEmbedding K δ hδ hδ0 (star x) =
      star (quadraticComplexEmbedding K δ hδ hδ0 x) := by
  change K.subtype (QuadraticModel.CM.cmQuadraticMap K δ hδ (star x)) = star (K.subtype (QuadraticModel.CM.cmQuadraticMap K δ hδ x))
  rw [QuadraticModel.CM.cm_quadratic_map_star]
  exact ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_coe K _

def rationalBallUnit (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) :
    (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (maximalRealSubfield K)
      (QuadraticModel.CM.cmQuadraticParameter K δ hδ)))ˣ :=
  Units.map ((QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm.toRingHom.mapMatrix).toMonoidHom
    (Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv g))

theorem rational_ball_unit_val (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) :
    (rationalBallUnit K δ hδ hδ0 g).val =
      (LinearMap.toMatrix' g.toLinearMap).map (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm := rfl

theorem rational_ball_unit_complex (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) :
    (rationalBallUnit K δ hδ hδ0 g).val.map (quadraticComplexEmbedding K δ hδ hδ0) =
      BallActionMatrix.CM.ballActionMatrix K g := by
  ext i j
  change K.subtype ((QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0)
    ((QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm (LinearMap.toMatrix' g.toLinearMap i j))) = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

theorem cm_hermitian_unit_complex_scalar (β : K)
    (hβ : IsCMField.complexConj K β = β) (hβ0 : β ≠ 0) :
    (CMGlobalFrames.CM.cmHermitianUnit K δ hδ β hβ hβ0).val.map
      (quadraticComplexEmbedding K δ hδ hδ0) =
        Matrix.diagonal (fun i => if i = 2 then (β : ℂ) else 1) := by
  rw [CMGlobalFrames.CM.cm_hermitian_unit_val K δ hδ hδ0]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.map_apply, QuadraticTensor.CM.quadraticHermitianMatrix, Matrix.diagonal_apply_eq]
    change K.subtype ((QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0)
      ((QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm (if i = 2 then β else 1))) = if i = 2 then (β : ℂ) else 1
    rw [AlgEquiv.apply_symm_apply]
    split_ifs <;> rfl
  · simp [QuadraticTensor.CM.quadraticHermitianMatrix, hij]

theorem cm_hermitian_unit_complex (B : HeckeCycles.GeometricSource.CM.BallDatum K) :
    (CMGlobalFrames.CM.cmHermitianUnit K δ hδ B.b B.conjugate_b
      (fun hb => (ne_of_lt B.negative) (by simp [hb]))).val.map
      (quadraticComplexEmbedding K δ hδ hδ0) = BallActionMatrix.CM.ballHermitianMatrix K B :=
  cm_hermitian_unit_complex_scalar K δ hδ hδ0 B.b B.conjugate_b
    (fun hb => (ne_of_lt B.negative) (by simp [hb]))

theorem rational_ball_unit_preserves (B : HeckeCycles.GeometricSource.CM.BallDatum K) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K)
    (hg : ∀ x y, HeckeCycles.GeometricSource.CM.hermitian K B.b (g x) (g y) = HeckeCycles.GeometricSource.CM.hermitian K B.b x y) :
    let H := CMGlobalFrames.CM.cmHermitianUnit K δ hδ B.b B.conjugate_b
      (fun hb => (ne_of_lt B.negative) (by simp [hb]))
    (rationalBallUnit K δ hδ hδ0 g).val.conjTranspose * H.val *
      (rationalBallUnit K δ hδ hδ0 g).val = H.val := by
  dsimp only
  let H := CMGlobalFrames.CM.cmHermitianUnit K δ hδ B.b B.conjugate_b
    (fun hb => (ne_of_lt B.negative) (by simp [hb]))
  let A := (rationalBallUnit K δ hδ hδ0 g).val
  let f := quadraticComplexEmbedding K δ hδ hδ0
  have he : (A.conjTranspose * H.val * A).map f = H.val.map f := by
    rw [Matrix.map_mul, Matrix.map_mul,
      Matrix.conjTranspose_map f (quadratic_complex_embedding_star K δ hδ hδ0)]
    change (A.map f).conjTranspose * H.val.map f * A.map f = H.val.map f
    rw [rational_ball_unit_complex, cm_hermitian_unit_complex]
    exact BallActionMatrix.CM.ball_action_matrix_unitary K B g hg
  apply Matrix.ext
  intro i j
  exact quadratic_complex_embedding_injective K δ hδ hδ0 (congrArg (fun M => M i j) he)

theorem rational_ball_unit_det (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : LinearMap.det g.toLinearMap = 1) :
    Matrix.GeneralLinearGroup.det (rationalBallUnit K δ hδ hδ0 g) = 1 := by
  apply matrix_unit_det_eq_one
  rw [rational_ball_unit_val]
  have he := RingHom.map_det (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm.toRingHom
    (LinearMap.toMatrix' g.toLinearMap)
  rw [LinearMap.det_toMatrix', hg, map_one] at he
  exact he.symm

def rationalBallSU (B : HeckeCycles.GeometricSource.CM.BallDatum K) (N : ℕ) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K)
    (hg : B.principalLevel N g) :
    RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (CMGlobalFrames.CM.cmHermitianUnit K δ hδ B.b B.conjugate_b
      (fun hb => (ne_of_lt B.negative) (by simp [hb]))).val :=
  ⟨rationalBallUnit K δ hδ hδ0 g, rational_ball_unit_preserves K δ hδ hδ0 B g hg.1,
    rational_ball_unit_det K δ hδ hδ0 g hg.2.1⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalBallUnitary.CM
