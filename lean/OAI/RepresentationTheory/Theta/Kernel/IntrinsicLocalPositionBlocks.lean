import OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussianCoordinates

/-! # Intrinsic Local Position Blocks -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalPositionBlocks.Intrinsic

noncomputable section

/-! Actual local position inclusions and projections form a complete
block decomposition. Their transposes construct global momentum
coordinates dual to the given native position coordinates. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalGaussianCoordinates.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d m H K} (B : Adelic.DataTheta.ComparisonData F H K A)

theorem local_position_row_column (v w : Fin A.places) :
    IntrinsicLocalGaussianCoordinates.Intrinsic.localPositionRow B v * IntrinsicLocalGaussianCoordinates.Intrinsic.localPositionColumn B w = if v = w then 1 else 0 := by
  by_cases hvw : v = w
  · subst w
    rw [ite_eq_left rfl,IntrinsicLocalGaussianCoordinates.Intrinsic.local_position_left_inverse]
  · rw [ite_eq_right hvw]
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    change (IntrinsicLocalGaussianCoordinates.Intrinsic.localPositionRow B v * IntrinsicLocalGaussianCoordinates.Intrinsic.localPositionColumn B w).mulVec x =
      (0 : Matrix (Fin (3 * m)) (Fin (3 * m)) ℝ).mulVec x
    rw [← Matrix.mulVec_mulVec,IntrinsicLocalGaussianCoordinates.Intrinsic.local_position_row_apply,IntrinsicLocalGaussianCoordinates.Intrinsic.local_position_column_apply,
      B.realPosition.symm_apply_apply,Matrix.zero_mulVec]
    simp [hvw]

theorem local_position_components (x : Adelic.BallGeometryData.RealPositions A) :
    B.realPosition x = ∑ v : Fin A.places, (IntrinsicLocalGaussianCoordinates.Intrinsic.localPositionColumn B v).mulVec (x v) := by
  simp only [IntrinsicLocalGaussianCoordinates.Intrinsic.local_position_column_apply,← map_sum]
  congr 1
  exact (Finset.univ_sum_single x).symm

def globalMomentum (p : Fin A.places → Fin (3 * m) → ℂ) : Adelic.BallGeometryData.FrameIndex A → ℂ :=
  ∑ v : Fin A.places, ((IntrinsicLocalGaussianCoordinates.Intrinsic.localPositionRow B v).map Complex.ofRealHom)ᵀ.mulVec (p v)

theorem local_momentum_component (v : Fin A.places) (p : Fin A.places → Fin (3 * m) → ℂ) :
    IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianJacobi B v (globalMomentum B p) = p v := by
  unfold IntrinsicLocalGaussianCoordinates.Intrinsic.localGaussianJacobi globalMomentum
  rw [Matrix.mulVec_sum]
  have hterm (w : Fin A.places) :
      ((IntrinsicLocalGaussianCoordinates.Intrinsic.localPositionColumn B v).map Complex.ofRealHom)ᵀ.mulVec
        (((IntrinsicLocalGaussianCoordinates.Intrinsic.localPositionRow B w).map Complex.ofRealHom)ᵀ.mulVec (p w)) = if w = v then p w else 0 := by
    rw [Matrix.mulVec_mulVec,← Matrix.transpose_mul,← Matrix.map_mul,local_position_row_column]
    split_ifs <;> simp
  simp only [hterm]
  simp

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalPositionBlocks.Intrinsic
