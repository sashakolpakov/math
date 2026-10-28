import OAI.RepresentationTheory.Theta.Adelic.ComplexPhaseCoordinates
import OAI.RepresentationTheory.Theta.Adelic.FieldFrameTransport

/-! # Intrinsic Real Phase -/

namespace OAI.RepresentationTheory.Theta.Adelic.IntrinsicRealPhase.Intrinsic

noncomputable section

/-! The actual native tensor frames give every real phase vector,
and the constructed real coordinates preserve their trace form. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.PhaseCoordinates OAI.RepresentationTheory.Theta.Adelic.FieldFrameTransport

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

def nativeRealPhaseEquiv :
    (∀ v : Fin A.places, Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) d) 3 m) ≃+
      ((BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℝ) :=
  (AddEquiv.piCongrRight (fun v =>
    (P.localFrame (.inl (A.enumerate v))).coordinates.toAddEquiv.trans
      (AddEquiv.piCongrRight (fun _ => (A.real v).toAddEquiv)))).trans
        (PhaseCoordinates.realPhaseCoordinates A).toLinearEquiv.toAddEquiv

theorem real_local_frame_pairing (v : Fin A.places)
    (x y : Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) d) 3 m) :
    DataTheta.standardPairing
      (fun j => A.real v ((P.localFrame (.inl (A.enumerate v))).coordinates x j))
      (fun j => A.real v ((P.localFrame (.inl (A.enumerate v))).coordinates y j)) =
    A.real v (Weil.AdelicSplitting.TensorSpace.Construction.tracePairing (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) d) 3 m
      (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl (A.enumerate v)))
      (Weil.AdelicSplitting.Integral.Construction.localizedForm F K.val (.inl (A.enumerate v))) x y) := by
  calc
    _ = Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing 3 m
        (FieldFrameTransport.fieldPhaseEquiv (A.real v) ((P.localFrame (.inl (A.enumerate v))).coordinates x))
        (FieldFrameTransport.fieldPhaseEquiv (A.real v) ((P.localFrame (.inl (A.enumerate v))).coordinates y)) := by
      rw [PhaseCoordinates.native_coordinatePairing_sum]
      simp only [DataTheta.standardPairing, Finset.sum_sub_distrib]
      rfl
    _ = _ := (FieldFrameTransport.coordinatePairing_field (A.real v) _ _).trans
      (congrArg (A.real v) ((P.localFrame (.inl (A.enumerate v))).preserves x y))

theorem nativeRealPhaseEquiv_pairing
    (x y : ∀ v : Fin A.places,
      Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) d) 3 m) :
    DataTheta.standardPairing (nativeRealPhaseEquiv A P x) (nativeRealPhaseEquiv A P y) =
      ∑ v, A.real v (Weil.AdelicSplitting.TensorSpace.Construction.tracePairing (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) d) 3 m
        (Weil.AdelicSplitting.Integral.Construction.localizedForm F H.val (.inl (A.enumerate v)))
        (Weil.AdelicSplitting.Integral.Construction.localizedForm F K.val (.inl (A.enumerate v))) (x v) (y v)) := by
  change DataTheta.standardPairing
    (PhaseCoordinates.realPhaseCoordinates A (fun v j => A.real v
      ((P.localFrame (.inl (A.enumerate v))).coordinates (x v) j)))
    (PhaseCoordinates.realPhaseCoordinates A (fun v j => A.real v
      ((P.localFrame (.inl (A.enumerate v))).coordinates (y v) j))) = _
  rw [PhaseCoordinates.realPhaseCoordinates_pairing]
  exact Finset.sum_congr rfl (fun v _ => real_local_frame_pairing A P v (x v) (y v))

end

end OAI.RepresentationTheory.Theta.Adelic.IntrinsicRealPhase.Intrinsic
