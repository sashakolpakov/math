import OAI.RepresentationTheory.Theta.Adelic.HodgeBlocks
import OAI.RepresentationTheory.Theta.Adelic.GeometricFrame

/-! # Geometric Frame Cocycle -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.GeometricFrameCocycle.HodgeCovariance

/-! Covariance and determinant of the actual geometric Hodge frame,
including every definite place and every multiplicity line. -/

open scoped Classical _root_.NumberField

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.RationalSU
open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.GeometricGroup OAI.RepresentationTheory.Theta.Adelic.GeometricFrame OAI.RepresentationTheory.Theta.Adelic.BallFramePositivity.RankThreeHodgeAction
open OAI.RepresentationTheory.Theta.Adelic.HodgeBlocks OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

theorem distinguished_inverse_matrix (g : RationalSU.ArchimedeanSU F H) :
    ((BallNatural.asSL (GeometricGroup.geometricBallHom A g))⁻¹).val =
      (BallGeometryData.standardMatrix A g A.distinguished)⁻¹ := by
  rw [Matrix.inv_def, HodgeBlocks.standardMatrix_det]
  simp only [Ring.inverse_one, one_smul]
  rfl

theorem geometric_hodge_block_covariance (g : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball)
    (a : BallGeometryData.FrameIndex A → ℂ) :
    BallGeometryData.geometricAction A g (BallGeometryData.geometricFrame A z a) =
      BallGeometryData.geometricFrame A (GeometricGroup.geometricBallHom A g • z) ((HodgeBlocks.hodgeBlockMatrix A g z).mulVec a) := by
  funext v
  apply Prod.ext
  · funext ij
    rcases ij with ⟨i, j⟩
    by_cases hv : v = A.distinguished
    · subst v
      simp only [BallGeometryData.geometricAction, BallGeometryData.geometricFrame]
      rw [HodgeBlocks.hodgeBlockMatrix_mulVec]
      simp only [HodgeBlocks.hodgeBlock]
      exact congrFun (BallFramePositivity.RankThreeHodgeAction.standard_hodge_transform (GeometricGroup.geometricBallHom A g) z
        (fun k => a (A.distinguished, k, j))) i
    · simp only [BallGeometryData.geometricAction, BallGeometryData.geometricFrame, ite_eq_right hv]
      by_cases hp : A.positive v j
      · simp only [ite_eq_left hp]
        rw [HodgeBlocks.hodgeBlockMatrix_mulVec]
        simp only [HodgeBlocks.hodgeBlock, ite_eq_right hv, ite_eq_left hp]
        rfl
      · simp [hp]
  · funext ij
    rcases ij with ⟨i, j⟩
    by_cases hv : v = A.distinguished
    · subst v
      simp only [BallGeometryData.geometricAction, BallGeometryData.geometricFrame]
      rw [HodgeBlocks.hodgeBlockMatrix_mulVec, HodgeBlocks.hodgeBlockMatrix_mulVec]
      simp only [HodgeBlocks.hodgeBlock]
      have h := congrFun (BallFramePositivity.RankThreeHodgeAction.dual_hodge_transform (GeometricGroup.geometricBallHom A g) z
        (fun k => a (A.distinguished, k, j))) i
      rw [distinguished_inverse_matrix] at h
      exact h
    · simp only [BallGeometryData.geometricAction, BallGeometryData.geometricFrame, ite_eq_right hv]
      by_cases hp : A.positive v j
      · simp [hp]
      · simp only [ite_eq_right hp]
        rw [HodgeBlocks.hodgeBlockMatrix_mulVec]
        simp only [HodgeBlocks.hodgeBlock, ite_eq_right hv, ite_eq_right hp]
        rfl

theorem frameMatrix_eq_hodgeBlockMatrix (g : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball) :
    BallGeometryData.frameMatrix A g z = HodgeBlocks.hodgeBlockMatrix A g z := by
  apply Matrix.ext
  intro i j
  change BallGeometryData.geometricCoordinates A (BallGeometryData.geometricAction A g (BallGeometryData.geometricFrame A z (Pi.single j 1))) i = _
  rw [geometric_hodge_block_covariance, GeometricFrame.geometric_coordinates_frame]
  simp only [Matrix.mulVec_single_one, Matrix.col_apply]

theorem geometric_frame_covariance (g : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball)
    (a : BallGeometryData.FrameIndex A → ℂ) :
    BallGeometryData.geometricAction A g (BallGeometryData.geometricFrame A z a) =
      BallGeometryData.geometricFrame A (GeometricGroup.geometricBallHom A g • z) ((BallGeometryData.frameMatrix A g z).mulVec a) := by
  rw [frameMatrix_eq_hodgeBlockMatrix]
  exact geometric_hodge_block_covariance A g z a

theorem geometric_frame_determinant (g : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball) :
    (BallGeometryData.frameMatrix A g z).det =
      DeterminantCoordinates.hodgeDeterminantFactor (BallNatural.asSL (GeometricGroup.geometricBallHom A g)) z.val ^ m := by
  rw [frameMatrix_eq_hodgeBlockMatrix]
  exact HodgeBlocks.hodgeBlockMatrix_det A g z

end RepresentationTheory.Theta.Adelic.GeometricFrameCocycle.HodgeCovariance

namespace RepresentationTheory.Theta.Adelic.GeometricFrameCocycle

/-! The actual Hodge frame and its dual satisfy the group cocycle laws. -/

open scoped Classical _root_.NumberField

open _root_.Matrix OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.RationalSU
open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallNatural.Factors OAI.RepresentationTheory.Theta.Adelic.GeometricGroup OAI.RepresentationTheory.Theta.Adelic.GeometricFrame
open OAI.RepresentationTheory.Theta.Adelic.GeometricFrameCocycle.HodgeCovariance OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

theorem standardMatrix_one (v : Fin A.places) : BallGeometryData.standardMatrix A 1 v = 1 :=
  congrArg Units.val (map_one (GeometricGroup.standardUnit A v))

theorem standardMatrix_mul (g h : RationalSU.ArchimedeanSU F H) (v : Fin A.places) :
    BallGeometryData.standardMatrix A (g * h) v = BallGeometryData.standardMatrix A g v * BallGeometryData.standardMatrix A h v :=
  congrArg Units.val (map_mul (GeometricGroup.standardUnit A v) g h)

theorem standardMatrix_inv (g : RationalSU.ArchimedeanSU F H) (v : Fin A.places) :
    BallGeometryData.standardMatrix A g⁻¹ v = (BallGeometryData.standardMatrix A g v)⁻¹ := by
  change (GeometricGroup.standardUnit A v g⁻¹).val = (GeometricGroup.standardUnit A v g).val⁻¹
  rw [map_inv, Matrix.coe_units_inv]

theorem geometricAction_one (w : BallGeometryData.ComplexPhase A) : BallGeometryData.geometricAction A 1 w = w := by
  funext v
  apply Prod.ext <;> funext ij
  · change (BallGeometryData.standardMatrix A 1 v).mulVec (fun k => (w v).1 (k, ij.2)) ij.1 = _
    rw [standardMatrix_one, Matrix.one_mulVec]
  · change ((BallGeometryData.standardMatrix A 1 v)⁻¹)ᵀ.mulVec (fun k => (w v).2 (k, ij.2)) ij.1 = _
    rw [standardMatrix_one, inv_one, Matrix.transpose_one, Matrix.one_mulVec]

theorem geometricAction_mul (g h : RationalSU.ArchimedeanSU F H) (w : BallGeometryData.ComplexPhase A) :
    BallGeometryData.geometricAction A (g * h) w = BallGeometryData.geometricAction A g (BallGeometryData.geometricAction A h w) := by
  funext v
  apply Prod.ext <;> funext ij
  · change (BallGeometryData.standardMatrix A (g * h) v).mulVec (fun k => (w v).1 (k, ij.2)) ij.1 =
      (BallGeometryData.standardMatrix A g v).mulVec
        ((BallGeometryData.standardMatrix A h v).mulVec (fun k => (w v).1 (k, ij.2))) ij.1
    rw [standardMatrix_mul, Matrix.mulVec_mulVec]
  · change ((BallGeometryData.standardMatrix A (g * h) v)⁻¹)ᵀ.mulVec (fun k => (w v).2 (k, ij.2)) ij.1 =
      ((BallGeometryData.standardMatrix A g v)⁻¹)ᵀ.mulVec
        (((BallGeometryData.standardMatrix A h v)⁻¹)ᵀ.mulVec (fun k => (w v).2 (k, ij.2))) ij.1
    rw [← standardMatrix_inv, _root_.mul_inv_rev, standardMatrix_mul, Matrix.transpose_mul,
      standardMatrix_inv, standardMatrix_inv, Matrix.mulVec_mulVec]

theorem frameMatrix_one (z : BallNatural.Ball) : BallGeometryData.frameMatrix A 1 z = 1 := by
  ext i j
  change BallGeometryData.geometricCoordinates A (BallGeometryData.geometricAction A 1 (BallGeometryData.geometricFrame A z (Pi.single j 1))) i = _
  rw [geometricAction_one, GeometricFrame.geometric_coordinates_frame]
  simp [Matrix.one_apply, Pi.single_apply]

theorem frameMatrix_mul (g h : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball) :
    BallGeometryData.frameMatrix A (g * h) z =
      BallGeometryData.frameMatrix A g (GeometricGroup.geometricBallHom A h • z) * BallGeometryData.frameMatrix A h z := by
  have he (a : BallGeometryData.FrameIndex A → ℂ) := HodgeCovariance.geometric_frame_covariance A (g * h) z a
  have hv (a : BallGeometryData.FrameIndex A → ℂ) :
      (BallGeometryData.frameMatrix A (g * h) z).mulVec a =
        (BallGeometryData.frameMatrix A g (GeometricGroup.geometricBallHom A h • z) * BallGeometryData.frameMatrix A h z).mulVec a := by
    apply GeometricFrame.geometricFrame_injective A (GeometricGroup.geometricBallHom A (g * h) • z)
    rw [← he, geometricAction_mul, HodgeCovariance.geometric_frame_covariance, HodgeCovariance.geometric_frame_covariance,
      map_mul, mul_smul, Matrix.mulVec_mulVec]
  ext i j
  have h := congrFun (hv (Pi.single j 1)) i
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using h

theorem frameMatrix_det_nonzero (g : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball) :
    (BallGeometryData.frameMatrix A g z).det ≠ 0 := by
  rw [HodgeCovariance.geometric_frame_determinant, DeterminantCoordinates.hodgeDeterminantFactor_eq]
  exact pow_ne_zero _ (pow_ne_zero _ (BallNatural.denominator_ne_zero _ _))

theorem dualFrameChange_one (z : BallNatural.Ball) (v : BallGeometryData.FrameIndex A → ℂ) :
    BallGeometryData.dualFrameChange A 1 z v = v := by
  simp only [BallGeometryData.dualFrameChange, frameMatrix_one, inv_one, Matrix.transpose_one, Matrix.one_mulVec]

theorem dualFrameChange_mul (g h : RationalSU.ArchimedeanSU F H) (z : BallNatural.Ball) (v : BallGeometryData.FrameIndex A → ℂ) :
    BallGeometryData.dualFrameChange A (g * h) z v =
      BallGeometryData.dualFrameChange A g (GeometricGroup.geometricBallHom A h • z) (BallGeometryData.dualFrameChange A h z v) := by
  simp only [BallGeometryData.dualFrameChange, frameMatrix_mul, Matrix.mulVec_mulVec]
  rw [Matrix.mul_inv_rev, Matrix.transpose_mul]

end RepresentationTheory.Theta.Adelic.GeometricFrameCocycle

end

end OAI
