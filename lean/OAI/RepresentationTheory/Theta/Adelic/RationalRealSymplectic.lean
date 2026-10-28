import OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction
import OAI.RepresentationTheory.Theta.Adelic.RationalSymplecticAction
import OAI.RepresentationTheory.Weil.AdelicSplitting.BaseChange

/-! # Rational Real Symplectic -/

namespace OAI.RepresentationTheory.Theta.Adelic.RationalRealSymplectic

noncomputable section

/-! The real Siegel matrix of a rational special-unitary element is
the scalar extension of its actual rational Siegel matrix. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Weil.AdelicSplitting.BaseChange.Construction
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.PhaseCoordinates OAI.RepresentationTheory.Theta.Adelic.BilinearCoordinates.Symplectic
open OAI.RepresentationTheory.Theta.Adelic.RealSymplecticAction OAI.RepresentationTheory.Theta.Adelic.RationalSymplecticAction

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

theorem localSUToPair_rational (g : SpecialUnitary.SU H.val) (v : Fin A.places) :
    FiniteSchwartz.localSUToPair F H K (.inl (A.enumerate v))
      (RationalSU.rationalArchimedeanSU F H g (A.enumerate v)) =
      Weil.AdelicSplitting.Integral.Construction.rationalPairLocal F H.val K.val (.inl (A.enumerate v)) (SpecialUnitary.includeUnitary H.val g, 1) := by
  apply Prod.ext
  · rfl
  · exact (map_one (Weil.AdelicSplitting.Integral.Construction.rationalUnitaryLocal F K.val (.inl (A.enumerate v)))).symm

theorem realNativeAction_principal (g : SpecialUnitary.SU H.val) (x : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace F (3 * m)) (v : Fin A.places) :
    RealSymplecticAction.realNativeAction A P (RationalSU.rationalArchimedeanSU F H g)
      (fun v j => A.real v (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) (x j))) v =
      fun i => A.real v (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v))
        (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P.rational (SpecialUnitary.includeUnitary H.val g, 1)) x i)) := by
  rw [RealSymplecticAction.realNativeAction_apply]
  have he : (fun j => (A.real v).symm (A.real v (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) (x j)))) =
      fun j => Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) (x j) := by
    funext j
    exact (A.real v).symm_apply_apply _
  rw [he, localSUToPair_rational, Weil.AdelicSplitting.BaseChange.Construction.localDualAction_rational]
  funext i
  exact congrArg (A.real v) ((RingHom.map_mulVec
    (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)))
    (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P.rational (SpecialUnitary.includeUnitary H.val g, 1)).val x i).symm)

theorem realCoordinateAction_rational (g : SpecialUnitary.SU H.val)
    (q : (BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℚ) :
    RealSymplecticAction.realCoordinateAction A P (RationalSU.rationalArchimedeanSU F H g) (fun i => (q i : ℝ)) =
      fun i => (RationalSymplecticAction.rationalCoordinateAction A P g q i : ℝ) := by
  obtain ⟨x, rfl⟩ := (PhaseCoordinates.rationalPhaseCoordinates A).surjective q
  have hx := funext (PhaseCoordinates.realPhaseCoordinates_rational A x)
  rw [← hx, RealSymplecticAction.realCoordinateAction_native]
  have hn := funext (realNativeAction_principal A P g x)
  rw [hn]
  have hy := funext (PhaseCoordinates.realPhaseCoordinates_rational A
    (Weil.Local.FunctionsMetaplectic.Construction.symplecticAction (Weil.AdelicSplitting.TensorSpace.Construction.dualPairSymplectic H.val K.val P.rational (SpecialUnitary.includeUnitary H.val g, 1)) x))
  rw [hy, RationalSymplecticAction.rational_native_action, RationalSymplecticAction.rationalCoordinateAction_native]

theorem realSiegelAction_rational (g : SpecialUnitary.SU H.val)
    (q : (BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℚ) :
    RealSymplecticAction.realSiegelAction A P (RationalSU.rationalArchimedeanSU F H g) (fun i => (q i : ℝ)) =
      fun i => (RationalSymplecticAction.rationalSiegelAction A P g q i : ℝ) := by
  rw [RealSymplecticAction.realSiegelAction, BilinearCoordinates.Symplectic.swapConjugate_apply]
  have hs : DataTheta.swapPhase (fun i => (q i : ℝ)) = fun i => ((DataTheta.swapPhase q i : ℚ) : ℝ) := by
    funext i
    cases i <;> rfl
  rw [hs, realCoordinateAction_rational]
  funext i
  cases i <;> rfl

theorem rational_real_symplectic_matrix (g : SpecialUnitary.SU H.val) :
    DataTheta.blockMatrix (RealSymplecticAction.realSymplecticBlocks A P (RationalSU.rationalArchimedeanSU F H g)) =
      (DataTheta.blockMatrix (RationalSymplecticAction.rationalSymplecticBlocks A P g)).map (algebraMap ℚ ℝ) := by
  rw [RealSymplecticAction.realSymplecticBlocks, RationalSymplecticAction.rationalSymplecticBlocks, BilinearCoordinates.Symplectic.blocks_matrix, BilinearCoordinates.Symplectic.blocks_matrix]
  exact BilinearCoordinates.Symplectic.linearSymplectic_rat_real _ _ _ _ (realSiegelAction_rational A P g)

end

end OAI.RepresentationTheory.Theta.Adelic.RationalRealSymplectic
