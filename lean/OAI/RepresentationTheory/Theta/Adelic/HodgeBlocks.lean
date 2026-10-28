import OAI.RepresentationTheory.Theta.Adelic.GeometricGroup
import OAI.RepresentationTheory.Theta.Adelic.BallFramePositivity

/-! # Hodge Blocks -/

namespace OAI.RepresentationTheory.Theta.Adelic.HodgeBlocks

noncomputable section

/-! The block matrix of the Hodge-frame representation at every real
place and on every multiplicity line, with its exact determinant. -/

open scoped Classical _root_.NumberField

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.RationalSU
open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.GeometricGroup OAI.RepresentationTheory.Theta.Adelic.BallFramePositivity.RankThreeHodgeAction OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

def hodgeBlock (g : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball) (v : Fin A.places) (j : Fin m) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  if v = A.distinguished then BallFramePositivity.RankThreeHodgeAction.hodgeFrameMatrix (GeometricGroup.geometricBallHom A g) z
  else if A.positive v j then BallGeometryData.standardMatrix A g v else (BallGeometryData.standardMatrix A g v)⁻¹.transpose

theorem standardMatrix_det (g : RationalSU.ArchimedeanSU F H) (v : Fin A.places) :
    (BallGeometryData.standardMatrix A g v).det = 1 :=
  congrArg Units.val (GeometricGroup.standardUnit_determinant A v g)

theorem hodgeBlock_det (g : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball) (v : Fin A.places) (j : Fin m) :
    (hodgeBlock A g z v j).det =
      if v = A.distinguished then DeterminantCoordinates.denominator (BallNatural.asSL (GeometricGroup.geometricBallHom A g)) z.val ^ 2 else 1 := by
  by_cases hv : v = A.distinguished
  · simp [hodgeBlock, hv, BallFramePositivity.RankThreeHodgeAction.hodgeFrameMatrix_det]
  · by_cases hp : A.positive v j
    · simp [hodgeBlock, hv, hp, standardMatrix_det]
    · simp [hodgeBlock, hv, hp, Matrix.det_nonsing_inv, standardMatrix_det]

def hodgeBlockIndex : (Fin 3 × (Fin A.places × Fin m)) ≃ BallGeometryData.FrameIndex A where
  toFun i := (i.2.1, i.1, i.2.2)
  invFun i := (i.2.1, i.1, i.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def hodgeBlockMatrix (g : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball) :
    Matrix (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ :=
  Matrix.reindex (hodgeBlockIndex A) (hodgeBlockIndex A)
    (Matrix.blockDiagonal (fun vj => hodgeBlock A g z vj.1 vj.2))

theorem hodgeBlockMatrix_det (g : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball) :
    (hodgeBlockMatrix A g z).det =
      DeterminantCoordinates.hodgeDeterminantFactor (BallNatural.asSL (GeometricGroup.geometricBallHom A g)) z.val ^ m := by
  rw [hodgeBlockMatrix, Matrix.det_reindex_self, Matrix.det_blockDiagonal]
  rw [Fintype.prod_prod_type]
  calc
    _ = ∏ v : Fin A.places, if v = A.distinguished then
        (DeterminantCoordinates.denominator (BallNatural.asSL (GeometricGroup.geometricBallHom A g)) z.val ^ 2) ^ m else 1 := by
      apply Finset.prod_congr rfl
      intro v _
      by_cases hv : v = A.distinguished <;> simp [hodgeBlock_det, hv]
    _ = _ := by simp [DeterminantCoordinates.hodgeDeterminantFactor_eq]

theorem hodgeBlockMatrix_mulVec (g : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball)
    (a : BallGeometryData.FrameIndex A → ℂ) (v : Fin A.places) (i : Fin 3) (j : Fin m) :
    (hodgeBlockMatrix A g z).mulVec a (v, i, j) =
      (hodgeBlock A g z v j).mulVec (fun k => a (v, k, j)) i := by
  change (∑ t : BallGeometryData.FrameIndex A,
    Matrix.blockDiagonal (fun vj => hodgeBlock A g z vj.1 vj.2)
      (i, v, j) ((hodgeBlockIndex A).symm t) * a t) = _
  have he := Equiv.sum_comp (hodgeBlockIndex A)
    (fun t : BallGeometryData.FrameIndex A =>
      Matrix.blockDiagonal (fun vj => hodgeBlock A g z vj.1 vj.2)
        (i, v, j) ((hodgeBlockIndex A).symm t) * a t)
  rw [← he]
  simp [Fintype.sum_prod_type, Matrix.blockDiagonal_apply, hodgeBlockIndex,
    Matrix.mulVec, dotProduct]

end

end OAI.RepresentationTheory.Theta.Adelic.HodgeBlocks
