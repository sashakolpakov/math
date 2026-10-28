import OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalPositionBlocks

/-! # Intrinsic Momentum Coordinates -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicMomentumCoordinates.Intrinsic

noncomputable section

/-! The dual local momentum coordinates are mutually inverse to the
native global momentum map. These identities use the actual position
equivalence and impose no additional coordinate compatibility. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussianCoordinates.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalPositionBlocks.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d m H K} (B : Adelic.DataTheta.ComparisonData F H K A)

theorem local_position_complete :
    (∑ v : Fin A.places, IntrinsicLocalGaussianCoordinates.Intrinsic.localPositionColumn B v * IntrinsicLocalGaussianCoordinates.Intrinsic.localPositionRow B v) = 1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  change (∑ v : Fin A.places, IntrinsicLocalGaussianCoordinates.Intrinsic.localPositionColumn B v * IntrinsicLocalGaussianCoordinates.Intrinsic.localPositionRow B v).mulVec x =
    (1 : Matrix (Adelic.BallGeometryData.FrameIndex A) (Adelic.BallGeometryData.FrameIndex A) ℝ).mulVec x
  rw [Matrix.sum_mulVec,Matrix.one_mulVec]
  simp only [← Matrix.mulVec_mulVec,IntrinsicLocalGaussianCoordinates.Intrinsic.local_position_row_apply]
  exact (IntrinsicLocalPositionBlocks.Intrinsic.local_position_components B (B.realPosition.symm x)).symm.trans (B.realPosition.apply_symm_apply x)

theorem global_momentum_components (p : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    IntrinsicLocalPositionBlocks.Intrinsic.globalMomentum B (fun v => IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianJacobi B v p) = p := by
  have hsum : (∑ v : Fin A.places, (IntrinsicLocalGaussianCoordinates.Intrinsic.localPositionColumn B v * IntrinsicLocalGaussianCoordinates.Intrinsic.localPositionRow B v).map Complex.ofRealHom) =
      (∑ v : Fin A.places, IntrinsicLocalGaussianCoordinates.Intrinsic.localPositionColumn B v * IntrinsicLocalGaussianCoordinates.Intrinsic.localPositionRow B v).map Complex.ofRealHom := by
    ext i j
    simp only [Matrix.sum_apply,Matrix.map_apply,map_sum]
  unfold IntrinsicLocalPositionBlocks.Intrinsic.globalMomentum IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianJacobi
  simp only [Matrix.mulVec_mulVec,← Matrix.transpose_mul,← Matrix.map_mul]
  rw [← Matrix.sum_mulVec,← Matrix.transpose_sum,hsum,local_position_complete,
    Matrix.map_one,Matrix.transpose_one,Matrix.one_mulVec]
  all_goals simp

theorem local_jacobi_joint_injective :
    Function.Injective (fun p : Adelic.BallGeometryData.FrameIndex A → ℂ => fun v => IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianJacobi B v p) := by
  intro p q h
  have he := congrArg (IntrinsicLocalPositionBlocks.Intrinsic.globalMomentum B) h
  simpa only [global_momentum_components] using he

def realMomentumComponent (p : Adelic.BallGeometryData.FrameIndex A → ℝ) (v : Fin A.places) : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m) :=
  (IntrinsicLocalGaussianCoordinates.Intrinsic.localPositionColumn B v)ᵀ.mulVec p

theorem real_momentum_component_cast (p : Adelic.BallGeometryData.FrameIndex A → ℝ) (v : Fin A.places) :
    IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianJacobi B v (fun i => (p i : ℂ)) = fun i => (realMomentumComponent B p v i : ℂ) := by
  funext i
  exact (Complex.ofRealHom.map_mulVec (IntrinsicLocalGaussianCoordinates.Intrinsic.localPositionColumn B v)ᵀ p i).symm

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicMomentumCoordinates.Intrinsic
