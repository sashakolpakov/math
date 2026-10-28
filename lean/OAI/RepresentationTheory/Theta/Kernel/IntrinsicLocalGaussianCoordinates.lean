import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSiegelRestriction
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicPlaceProjection

/-! # Intrinsic Local Gaussian Coordinates -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussianCoordinates.Intrinsic

noncomputable section

/-! Positive local Gaussian coordinates for an arbitrary full native
comparison. The actual real position map provides the inclusion and its
left inverse; the local Jacobi map is consequently surjective. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Kernel.IntrinsicSiegelRestriction.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d m H K} (B : Adelic.DataTheta.ComparisonData F H K A)

def localPositionColumn (v : Fin A.places) : Matrix (Adelic.BallGeometryData.FrameIndex A) (Fin (3 * m)) ℝ :=
  LinearMap.toMatrix' (B.realPosition.toLinearMap.comp
    (LinearMap.single ℝ (fun _ : Fin A.places => Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m)) v))

def localPositionRow (v : Fin A.places) : Matrix (Fin (3 * m)) (Adelic.BallGeometryData.FrameIndex A) ℝ :=
  LinearMap.toMatrix' ((LinearMap.proj v).comp B.realPosition.symm.toLinearMap)

theorem local_position_column_apply (v : Fin A.places) (x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m)) :
    (localPositionColumn B v).mulVec x = B.realPosition (Pi.single v x) :=
  LinearMap.toMatrix'_mulVec _ x

theorem local_position_row_apply (v : Fin A.places) (x : Adelic.BallGeometryData.FrameIndex A → ℝ) :
    (localPositionRow B v).mulVec x = B.realPosition.symm x v :=
  LinearMap.toMatrix'_mulVec _ x

theorem local_position_left_inverse (v : Fin A.places) :
    localPositionRow B v * localPositionColumn B v = 1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  change (localPositionRow B v * localPositionColumn B v).mulVec x = (1 : Matrix (Fin (3 * m)) _ ℝ).mulVec x
  rw [← Matrix.mulVec_mulVec,local_position_row_apply,local_position_column_apply,
    B.realPosition.symm_apply_apply,Pi.single_eq_same,Matrix.one_mulVec]

theorem local_position_column_injective (v : Fin A.places) :
    Function.Injective (localPositionColumn B v).mulVec := by
  intro x y h
  have he := congrArg (localPositionRow B v).mulVec h
  simpa only [Matrix.mulVec_mulVec,local_position_left_inverse,Matrix.one_mulVec] using he

def localGaussianPeriod (v : Fin A.places) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Adelic.BallGeometryData.FrameIndex A)) : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin (3 * m)) :=
  IntrinsicSiegelRestriction.Intrinsic.restrictedSiegel Z (localPositionColumn B v) (local_position_column_injective B v)

def localGaussianJacobi (v : Fin A.places) (ξ : Adelic.BallGeometryData.FrameIndex A → ℂ) : Fin (3 * m) → ℂ :=
  ((localPositionColumn B v).map Complex.ofRealHom)ᵀ.mulVec ξ

theorem local_gaussian_jacobi_surjective (v : Fin A.places) : Function.Surjective (localGaussianJacobi B v) := by
  intro η
  refine ⟨((localPositionRow B v).map Complex.ofRealHom)ᵀ.mulVec η,?_⟩
  change ((localPositionColumn B v).map Complex.ofRealHom)ᵀ.mulVec
    (((localPositionRow B v).map Complex.ofRealHom)ᵀ.mulVec η) = η
  rw [Matrix.mulVec_mulVec,← Matrix.transpose_mul,← Matrix.map_mul,local_position_left_inverse,
    Matrix.map_one,Matrix.transpose_one,Matrix.one_mulVec]
  all_goals simp

theorem local_gaussian_quadratic (v : Fin A.places) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Adelic.BallGeometryData.FrameIndex A))
    (x y : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m)) :
    AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (localGaussianPeriod B v Z).matrix x y =
      AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm Z.matrix (B.realPosition (Pi.single v x)) (B.realPosition (Pi.single v y)) := by
  change AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (IntrinsicSiegelRestriction.Intrinsic.realCongruence (localPositionColumn B v) Z.matrix) x y = _
  rw [IntrinsicSiegelRestriction.Intrinsic.realCongruence_form,local_position_column_apply,local_position_column_apply]

theorem local_gaussian_linear (v : Fin A.places) (ξ : Adelic.BallGeometryData.FrameIndex A → ℂ) (x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m)) :
    (∑ i, (x i : ℂ) * localGaussianJacobi B v ξ i) =
      ∑ i, (B.realPosition (Pi.single v x) i : ℂ) * ξ i := by
  have hx : ((localPositionColumn B v).map Complex.ofRealHom).mulVec (fun i => (x i : ℂ)) =
      fun i => (B.realPosition (Pi.single v x) i : ℂ) := by
    funext i
    exact (Complex.ofRealHom.map_mulVec (localPositionColumn B v) x i).symm.trans
      (congrArg (fun t : ℝ => (t : ℂ)) (congrFun (local_position_column_apply B v x) i))
  change (fun i => (x i : ℂ)) ⬝ᵥ (((localPositionColumn B v).map Complex.ofRealHom)ᵀ.mulVec ξ) = _
  rw [Matrix.dotProduct_transpose_mulVec,hx,dotProduct_comm]
  rfl

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussianCoordinates.Intrinsic
