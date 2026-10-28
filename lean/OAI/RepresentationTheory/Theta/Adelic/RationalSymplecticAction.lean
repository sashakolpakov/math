import OAI.RepresentationTheory.Theta.Adelic.BilinearCoordinates
import OAI.RepresentationTheory.Theta.Adelic.PhaseCoordinates

/-! # Rational Symplectic Action -/

namespace OAI.RepresentationTheory.Theta.Adelic.RationalSymplecticAction

noncomputable section

/-! Rational Siegel matrices are constructed from the actual rational
special-unitary tensor action and the trace-compatible phase coordinates. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary
open OAI.RepresentationTheory.Theta.Adelic.PhaseCoordinates OAI.RepresentationTheory.Theta.Adelic.BilinearCoordinates.Symplectic

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

def rationalCoordinateAction (g : SpecialUnitary.SU H.val) :
    ((BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℚ) ≃ₗ[ℚ] ((BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℚ) :=
  (PhaseCoordinates.rationalPhaseCoordinates A).symm.trans
    (((Weil.AdelicSplitting.TensorSpace.Construction.coordinateAction H.val K.val P.rational (SpecialUnitary.includeUnitary H.val g, 1)).restrictScalars ℚ).trans
      (PhaseCoordinates.rationalPhaseCoordinates A))

theorem rational_native_action (g : SpecialUnitary.SU H.val) (x : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace F (3 * m)) :
    Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P.rational (SpecialUnitary.includeUnitary H.val g, 1)) x =
      Weil.AdelicSplitting.TensorSpace.Construction.coordinateAction H.val K.val P.rational (SpecialUnitary.includeUnitary H.val g, 1) x := by
  change Matrix.toLin' (LinearMap.toMatrix'
    (Weil.AdelicSplitting.TensorSpace.Construction.coordinateAction H.val K.val P.rational (SpecialUnitary.includeUnitary H.val g, 1)).toLinearMap) x = _
  rw [Matrix.toLin'_toMatrix']
  rfl

theorem rationalCoordinateAction_native (g : SpecialUnitary.SU H.val) (x : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace F (3 * m)) :
    rationalCoordinateAction A P g (PhaseCoordinates.rationalPhaseCoordinates A x) =
      PhaseCoordinates.rationalPhaseCoordinates A (Weil.AdelicSplitting.TensorSpace.Construction.coordinateAction H.val K.val P.rational (SpecialUnitary.includeUnitary H.val g, 1) x) := by
  change PhaseCoordinates.rationalPhaseCoordinates A (Weil.AdelicSplitting.TensorSpace.Construction.coordinateAction H.val K.val P.rational
    (SpecialUnitary.includeUnitary H.val g, 1) ((PhaseCoordinates.rationalPhaseCoordinates A).symm (PhaseCoordinates.rationalPhaseCoordinates A x))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem rationalCoordinateAction_preserves (g : SpecialUnitary.SU H.val)
    (x y : (BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℚ) :
    DataTheta.standardPairing (rationalCoordinateAction A P g x) (rationalCoordinateAction A P g y) =
      DataTheta.standardPairing x y := by
  obtain ⟨u, rfl⟩ := (PhaseCoordinates.rationalPhaseCoordinates A).surjective x
  obtain ⟨v, rfl⟩ := (PhaseCoordinates.rationalPhaseCoordinates A).surjective y
  rw [rationalCoordinateAction_native, rationalCoordinateAction_native,
    PhaseCoordinates.rationalPhaseCoordinates_pairing, PhaseCoordinates.rationalPhaseCoordinates_pairing]
  exact congrArg (Algebra.trace ℚ F)
    (Weil.AdelicSplitting.TensorSpace.Construction.coordinateAction_preserves H.val K.val P.rational (SpecialUnitary.includeUnitary H.val g, 1) u v)

def rationalSiegelAction (g : SpecialUnitary.SU H.val) :
    ((BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℚ) ≃ₗ[ℚ] ((BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℚ) :=
  BilinearCoordinates.Symplectic.swapConjugate (rationalCoordinateAction A P g)

theorem rationalSiegelAction_preserves (g : SpecialUnitary.SU H.val)
    (x y : (BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℚ) :
    DataTheta.standardPairing (rationalSiegelAction A P g x) (rationalSiegelAction A P g y) = DataTheta.standardPairing x y :=
  BilinearCoordinates.Symplectic.swapConjugate_preserves _ (rationalCoordinateAction_preserves A P g) x y

def rationalSymplecticBlocks (g : SpecialUnitary.SU H.val) : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks (BallGeometryData.FrameIndex A) ℚ :=
  PoissonAutomorphyNormalizationData.blocks (BilinearCoordinates.Symplectic.linearSymplectic (rationalSiegelAction A P g) (rationalSiegelAction_preserves A P g))

theorem rationalSymplecticBlocks_action (g : SpecialUnitary.SU H.val) (x : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace F (3 * m)) :
    (DataTheta.blockMatrix (rationalSymplecticBlocks A P g)).mulVec (DataTheta.swapPhase (PhaseCoordinates.rationalPhaseCoordinates A x)) =
      DataTheta.swapPhase (PhaseCoordinates.rationalPhaseCoordinates A
        (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P.rational (SpecialUnitary.includeUnitary H.val g, 1)) x)) := by
  rw [rationalSymplecticBlocks, BilinearCoordinates.Symplectic.blocks_matrix, BilinearCoordinates.Symplectic.linearSymplectic_action]
  rw [rationalSiegelAction, BilinearCoordinates.Symplectic.swapConjugate_apply]
  have hs : DataTheta.swapPhase (DataTheta.swapPhase (PhaseCoordinates.rationalPhaseCoordinates A x)) = PhaseCoordinates.rationalPhaseCoordinates A x := by
    funext i
    cases i <;> rfl
  rw [hs, rationalCoordinateAction_native]
  rw [rational_native_action]

end

end OAI.RepresentationTheory.Theta.Adelic.RationalSymplecticAction
