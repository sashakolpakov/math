import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicPlaceMatrices
import OAI.RepresentationTheory.Theta.Adelic.PeriodCrossTerms

/-! # Intrinsic Period Blocks -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicPeriodBlocks.CM

noncomputable section

/-! In the actual native position coordinates, the geometric period
matrix is precisely the block matrix of its local real-place periods. -/

open scoped Classical _root_.NumberField
open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural
open OAI.RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition OAI.RepresentationTheory.Theta.Adelic.LocalPositionInclusion
open OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates OAI.RepresentationTheory.Theta.Adelic.SiegelRestriction

theorem siegel_form_basis_entry {I : Type} [Fintype I] [DecidableEq I]
    (Z : Matrix I I ℂ) (i j : I) :
    ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm Z (Pi.single i 1) (Pi.single j 1) = Z i j := by
  simp [ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm_apply, Pi.single_apply, apply_ite]

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W)

theorem native_position_unflatten_single (v : Fin A.places) (a : Fin 3 × Fin m) :
    IntrinsicPlaceMatrices.CM.nativePositionUnflatten A (Pi.single (v, a) 1) = Pi.single v (Pi.single (finProdFinEquiv a) 1) := by
  funext w j
  change (Pi.single (v, a) 1 : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℝ) (w, finProdFinEquiv.symm j) =
    (Pi.single v (Pi.single (finProdFinEquiv a) (1 : ℝ)) : RepresentationTheory.Theta.Adelic.BallGeometryData.RealPositions A) w j
  by_cases hw : w = v
  · subst w
    simp only [Pi.single_apply, Prod.mk.injEq, true_and, ite_true]
    simp only [Equiv.symm_apply_eq]
  · simp [hw]

theorem native_position_matrix_single (v : Fin A.places) (a : Fin 3 × Fin m) :
    (IntrinsicPlaceMatrices.CM.nativePositionMatrix A).val.mulVec (Pi.single (v, a) 1) =
      (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.realPositionColumn A v).mulVec (Pi.single (finProdFinEquiv a) 1) := by
  rw [IntrinsicPlaceMatrices.CM.native_position_matrix_apply, native_position_unflatten_single, RepresentationTheory.Theta.Adelic.LocalPositionInclusion.realPositionColumn_apply]

theorem native_period_block_matrix (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H W) (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) :
    RepresentationTheory.Theta.Adelic.SiegelRestriction.realCongruence (IntrinsicPlaceMatrices.CM.nativePositionMatrix A).val (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z).matrix =
      IntrinsicPlaceMatrices.CM.nativePlaceMatrix A (fun v => (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.localSiegelPeriod A P v z).matrix) := by
  apply Matrix.ext
  rintro ⟨v, a⟩ ⟨w, b⟩
  rw [← siegel_form_basis_entry
    (RepresentationTheory.Theta.Adelic.SiegelRestriction.realCongruence (IntrinsicPlaceMatrices.CM.nativePositionMatrix A).val (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z).matrix) (v, a) (w, b),
    RepresentationTheory.Theta.Adelic.SiegelRestriction.realCongruence_form, native_position_matrix_single,
    native_position_matrix_single, IntrinsicPlaceMatrices.CM.native_place_matrix_entry]
  by_cases hvw : v = w
  · subst w
    rw [ite_eq_left rfl]
    change ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z).matrix
      ((RepresentationTheory.Theta.Adelic.LocalPositionInclusion.realPositionColumn A v).mulVec (Pi.single (finProdFinEquiv a) 1))
      ((RepresentationTheory.Theta.Adelic.LocalPositionInclusion.realPositionColumn A v).mulVec (Pi.single (finProdFinEquiv b) 1)) =
      RepresentationTheory.Theta.Adelic.SiegelRestriction.realCongruence (RepresentationTheory.Theta.Adelic.LocalPositionInclusion.realPositionColumn A v) (RepresentationTheory.Theta.Adelic.PeriodCoordinates.geometricPeriod A P z).matrix
        (finProdFinEquiv a) (finProdFinEquiv b)
    rw [← RepresentationTheory.Theta.Adelic.SiegelRestriction.realCongruence_form, siegel_form_basis_entry]
  · rw [ite_eq_right hvw]
    exact RepresentationTheory.Theta.Adelic.PeriodCrossTerms.period_cross_terms_zero A P v w hvw z _ _

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicPeriodBlocks.CM
