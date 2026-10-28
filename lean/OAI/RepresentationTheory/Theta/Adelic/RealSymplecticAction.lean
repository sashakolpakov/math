import OAI.RepresentationTheory.Theta.Adelic.BilinearCoordinates
import OAI.RepresentationTheory.Theta.Adelic.PhaseCoordinates
import OAI.RepresentationTheory.Weil.Local.FieldFourier
import OAI.RepresentationTheory.Weil.AdelicSplitting.SchrodingerPairing

/-! # Real Symplectic Action -/

namespace OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction

noncomputable section

/-! The real Siegel action is the actual native tensor action,
transported through the constructed trace coordinates and phase swap. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Weil.Local.FieldFourier.Construction OAI.RepresentationTheory.Weil.AdelicSplitting.SchrodingerPairing.Construction
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.RationalSU
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.PhaseCoordinates OAI.RepresentationTheory.Theta.Adelic.BilinearCoordinates.Symplectic

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

def localRealSymplectic (g : RationalSU.ArchimedeanSU F H) (v : Fin A.places) : Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℝ (3 * m) :=
  Weil.Local.FieldFourier.Construction.fieldSymplecticMap (A.real v) (3 * m)
    (Weil.AdelicSplitting.Assembly.Construction.localDualAction F d 3 m H K P (.inl (A.enumerate v))
      (FiniteSchwartz.localSUToPair F H K (.inl (A.enumerate v)) (g (A.enumerate v))))

def realNativeAction (g : RationalSU.ArchimedeanSU F H) :
    (Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m)) ≃ₗ[ℝ] (Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m)) :=
  LinearEquiv.piCongrRight (fun v => Weil.AdelicSplitting.SchrodingerPairing.Construction.symplecticPhaseEquiv ℝ (3 * m) (localRealSymplectic A P g v))

theorem realNativeAction_apply (g : RationalSU.ArchimedeanSU F H)
    (x : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m)) (v : Fin A.places) :
    realNativeAction A P g x v = fun i => A.real v
      (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.AdelicSplitting.Assembly.Construction.localDualAction F d 3 m H K P (.inl (A.enumerate v))
        (FiniteSchwartz.localSUToPair F H K (.inl (A.enumerate v)) (g (A.enumerate v))))
          (fun j => (A.real v).symm (x v j)) i) := by
  have h := Weil.Local.FieldFourier.Construction.fieldSymplecticMap_action (A.real v)
    (Weil.AdelicSplitting.Assembly.Construction.localDualAction F d 3 m H K P (.inl (A.enumerate v))
      (FiniteSchwartz.localSUToPair F H K (.inl (A.enumerate v)) (g (A.enumerate v))))
    (fun j => (A.real v).symm (x v j))
  have he : (fun j => A.real v ((A.real v).symm (x v j))) = x v := by
    funext j
    exact (A.real v).apply_symm_apply _
  rw [he] at h
  exact h

def realCoordinateAction (g : RationalSU.ArchimedeanSU F H) :
    ((BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℝ) ≃ₗ[ℝ] ((BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℝ) :=
  (PhaseCoordinates.realPhaseCoordinates A).symm.toLinearEquiv.trans
    ((realNativeAction A P g).trans (PhaseCoordinates.realPhaseCoordinates A).toLinearEquiv)

theorem realCoordinateAction_native (g : RationalSU.ArchimedeanSU F H)
    (x : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m)) :
    realCoordinateAction A P g (PhaseCoordinates.realPhaseCoordinates A x) =
      PhaseCoordinates.realPhaseCoordinates A (realNativeAction A P g x) := by
  change PhaseCoordinates.realPhaseCoordinates A (realNativeAction A P g
    ((PhaseCoordinates.realPhaseCoordinates A).symm (PhaseCoordinates.realPhaseCoordinates A x))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]

theorem realCoordinateAction_preserves (g : RationalSU.ArchimedeanSU F H)
    (x y : (BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℝ) :
    DataTheta.standardPairing (realCoordinateAction A P g x) (realCoordinateAction A P g y) =
      DataTheta.standardPairing x y := by
  obtain ⟨u, rfl⟩ := (PhaseCoordinates.realPhaseCoordinates A).surjective x
  obtain ⟨v, rfl⟩ := (PhaseCoordinates.realPhaseCoordinates A).surjective y
  rw [realCoordinateAction_native, realCoordinateAction_native,
    PhaseCoordinates.realPhaseCoordinates_pairing, PhaseCoordinates.realPhaseCoordinates_pairing]
  exact Finset.sum_congr rfl (fun w _ =>
    BilinearCoordinates.Symplectic.symplectic_preserves_standard (localRealSymplectic A P g w) (u w) (v w))

def realSiegelAction (g : RationalSU.ArchimedeanSU F H) :
    ((BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℝ) ≃ₗ[ℝ] ((BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℝ) :=
  BilinearCoordinates.Symplectic.swapConjugate (realCoordinateAction A P g)

theorem realSiegelAction_preserves (g : RationalSU.ArchimedeanSU F H)
    (x y : (BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℝ) :
    DataTheta.standardPairing (realSiegelAction A P g x) (realSiegelAction A P g y) = DataTheta.standardPairing x y :=
  BilinearCoordinates.Symplectic.swapConjugate_preserves _ (realCoordinateAction_preserves A P g) x y

def realSymplecticBlocks (g : RationalSU.ArchimedeanSU F H) : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks (BallGeometryData.FrameIndex A) ℝ :=
  PoissonAutomorphyNormalizationData.blocks (BilinearCoordinates.Symplectic.linearSymplectic (realSiegelAction A P g) (realSiegelAction_preserves A P g))

theorem realSymplecticBlocks_action (g : RationalSU.ArchimedeanSU F H)
    (x : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m)) :
    (DataTheta.blockMatrix (realSymplecticBlocks A P g)).mulVec (DataTheta.swapPhase (PhaseCoordinates.realPhaseCoordinates A x)) =
      DataTheta.swapPhase (PhaseCoordinates.realPhaseCoordinates A (fun v i => A.real v
        (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.AdelicSplitting.Assembly.Construction.localDualAction F d 3 m H K P (.inl (A.enumerate v))
          (FiniteSchwartz.localSUToPair F H K (.inl (A.enumerate v)) (g (A.enumerate v))))
            (fun j => (A.real v).symm (x v j)) i))) := by
  rw [realSymplecticBlocks, BilinearCoordinates.Symplectic.blocks_matrix, BilinearCoordinates.Symplectic.linearSymplectic_action]
  rw [realSiegelAction, BilinearCoordinates.Symplectic.swapConjugate_apply]
  have hs : DataTheta.swapPhase (DataTheta.swapPhase (PhaseCoordinates.realPhaseCoordinates A x)) = PhaseCoordinates.realPhaseCoordinates A x := by
    funext i
    cases i <;> rfl
  rw [hs, realCoordinateAction_native]
  have hn := funext (fun v => realNativeAction_apply A P g x v)
  rw [hn]

end

end OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction
