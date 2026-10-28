import OAI.RepresentationTheory.Theta.Adelic.ComplexIntrinsicAction
import OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates

/-! # Period Place Projection -/

namespace OAI.RepresentationTheory.Theta.Adelic.PeriodPlaceProjection

noncomputable section

section

/-! Projection to one archimedean place in actual native, real, and
complex geometric coordinates. This makes the local decomposition of
the positive period graph explicit. -/

open scoped Classical _root_.NumberField

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.PhaseCoordinates
open OAI.RepresentationTheory.Theta.Adelic.IntrinsicRealPhase.Intrinsic OAI.RepresentationTheory.Theta.Adelic.ComplexIntrinsicAction.IntrinsicPhaseIntertwining OAI.RepresentationTheory.Theta.Adelic.ComplexPhaseCoordinates
open OAI.RepresentationTheory.Theta.Adelic.ComplexIntrinsicAction.Coordinate OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates

def placeProjection {R V W : Type} [Semiring R] [Fintype V] [DecidableEq V]
    [AddCommMonoid W] [Module R W] (v : V) : (V → W) →ₗ[R] (V → W) :=
  (LinearMap.single R (fun _ : V => W) v).comp (LinearMap.proj v)

@[simp] theorem placeProjection_apply {R V W : Type} [Semiring R] [Fintype V] [DecidableEq V]
    [AddCommMonoid W] [Module R W] (v : V) (x : V → W) :
    placeProjection (R := R) v x = Pi.single v (x v) := rfl

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

def realPlaceProjection (v : Fin A.places) :
    ((BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℝ) →ₗ[ℝ] ((BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℝ) :=
  LinearMap.comp (PhaseCoordinates.realPhaseCoordinates A).toLinearEquiv.toLinearMap
    (LinearMap.comp (placeProjection (R := ℝ) v) (PhaseCoordinates.realPhaseCoordinates A).symm.toLinearEquiv.toLinearMap)

def geometricPlaceProjection (v : Fin A.places) : BallGeometryData.ComplexPhase A →ₗ[ℂ] BallGeometryData.ComplexPhase A :=
  placeProjection v

theorem realPlaceProjection_native (v : Fin A.places) (x : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m)) :
    realPlaceProjection A v (PhaseCoordinates.realPhaseCoordinates A x) = PhaseCoordinates.realPhaseCoordinates A (Pi.single v (x v)) := by
  change PhaseCoordinates.realPhaseCoordinates A (placeProjection (R := ℝ) v
    ((PhaseCoordinates.realPhaseCoordinates A).symm (PhaseCoordinates.realPhaseCoordinates A x))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

theorem nativeRealPhase_projection (v : Fin A.places)
    (s : ∀ w : Fin A.places, Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate w)) d) 3 m) :
    realPlaceProjection A v (IntrinsicRealPhase.Intrinsic.nativeRealPhaseEquiv A P s) =
      IntrinsicRealPhase.Intrinsic.nativeRealPhaseEquiv A P (Pi.single v (s v)) := by
  rw [ComplexIntrinsicAction.IntrinsicPhaseIntertwining.nativeRealPhase_apply, ComplexIntrinsicAction.IntrinsicPhaseIntertwining.nativeRealPhase_apply, realPlaceProjection_native]
  apply congrArg (PhaseCoordinates.realPhaseCoordinates A)
  funext w i
  by_cases hw : w = v
  · subst w
    simp
  · simp [hw]

theorem geometric_native_projection (v : Fin A.places)
    (s : ∀ w : Fin A.places, Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate w)) d) 3 m) :
    geometricPlaceProjection A v (BallGeometryData.realTensorComponents A s) =
      BallGeometryData.realTensorComponents A (Pi.single v (s v)) := by
  funext w
  by_cases hw : w = v
  · subst w
    simp [geometricPlaceProjection, BallGeometryData.realTensorComponents]
  · apply Prod.ext <;> funext ij <;>
      simp [geometricPlaceProjection, BallGeometryData.realTensorComponents, hw, Matrix.mulVec, dotProduct]

theorem complex_place_projection (v : Fin A.places)
    (x : (BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℂ) :
    ComplexPhaseCoordinates.complexPhaseCoordinates A P (ComplexIntrinsicAction.Coordinate.complexifiedLinear (realPlaceProjection A v) x) =
      geometricPlaceProjection A v (ComplexPhaseCoordinates.complexPhaseCoordinates A P x) := by
  have hlinear : (ComplexPhaseCoordinates.complexPhaseCoordinates A P).toLinearEquiv.toLinearMap.comp
      (ComplexIntrinsicAction.Coordinate.complexifiedLinear (realPlaceProjection A v)) =
      (geometricPlaceProjection A v).comp (ComplexPhaseCoordinates.complexPhaseCoordinates A P).toLinearEquiv.toLinearMap := by
    apply ComplexIntrinsicAction.Coordinate.complexLinear_ext_real
    intro u
    obtain ⟨s, rfl⟩ := (IntrinsicRealPhase.Intrinsic.nativeRealPhaseEquiv A P).surjective u
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ComplexIntrinsicAction.Coordinate.complexifiedLinear_real, nativeRealPhase_projection]
    change ComplexPhaseCoordinates.complexPhaseCoordinates A P _ = geometricPlaceProjection A v (ComplexPhaseCoordinates.complexPhaseCoordinates A P _)
    have hs : ComplexPhaseCoordinates.complexPhaseCoordinates A P (fun i => (IntrinsicRealPhase.Intrinsic.nativeRealPhaseEquiv A P s i : ℂ)) =
        BallGeometryData.realTensorComponents A s := ComplexPhaseCoordinates.complexPhaseCoordinates_native A P s
    have ht : ComplexPhaseCoordinates.complexPhaseCoordinates A P
        (fun i => (IntrinsicRealPhase.Intrinsic.nativeRealPhaseEquiv A P (Pi.single v (s v)) i : ℂ)) =
        BallGeometryData.realTensorComponents A (Pi.single v (s v)) := ComplexPhaseCoordinates.complexPhaseCoordinates_native A P _
    rw [hs, ht]
    exact (geometric_native_projection A v s).symm
  exact LinearMap.congr_fun hlinear x

def framePlaceProjection (v : Fin A.places) (a : BallGeometryData.FrameIndex A → ℂ) : BallGeometryData.FrameIndex A → ℂ :=
  fun i => if i.1 = v then a i else 0

theorem geometric_frame_projection (v : Fin A.places) (z : BallNatural.Ball) (a : BallGeometryData.FrameIndex A → ℂ) :
    geometricPlaceProjection A v (BallGeometryData.geometricFrame A z a) =
      BallGeometryData.geometricFrame A z (framePlaceProjection A v a) := by
  funext w
  by_cases hw : w = v
  · subst w
    simp [geometricPlaceProjection, BallGeometryData.geometricFrame, framePlaceProjection]
  · apply Prod.ext <;> funext ij <;>
      simp [geometricPlaceProjection, BallGeometryData.geometricFrame, framePlaceProjection, hw]

theorem coordinate_frame_projection (v : Fin A.places) (z : BallNatural.Ball) (a : BallGeometryData.FrameIndex A → ℂ) :
    ComplexIntrinsicAction.Coordinate.complexifiedLinear (realPlaceProjection A v) ((PeriodCoordinates.coordinateHodgeMatrix A P z).mulVec a) =
      (PeriodCoordinates.coordinateHodgeMatrix A P z).mulVec (framePlaceProjection A v a) := by
  apply (ComplexPhaseCoordinates.complexPhaseCoordinates A P).injective
  rw [complex_place_projection, PeriodCoordinates.complex_coordinate_frame, PeriodCoordinates.complex_coordinate_frame,
    geometric_frame_projection]

end

/-! The projection to each place is self-adjoint for the trace
symplectic pairing and preserves the actual positive period graph. -/

open scoped Classical _root_.NumberField

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.GeometricTracePairing OAI.RepresentationTheory.Theta.Adelic.ComplexSymplecticPairing
open OAI.RepresentationTheory.Theta.Adelic.ComplexPhaseCoordinates OAI.RepresentationTheory.Theta.Adelic.ComplexIntrinsicAction.Coordinate OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

theorem geometric_projection_pairing (v : Fin A.places) (x y : BallGeometryData.ComplexPhase A) :
    GeometricTracePairing.geometricPairing A (geometricPlaceProjection A v x) y =
      GeometricTracePairing.geometricPairing A x (geometricPlaceProjection A v y) := by
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : w = v
  · subst w
    simp [geometricPlaceProjection, placeProjection]
  · simp [geometricPlaceProjection, placeProjection, hw]

include P in
theorem complex_projection_pairing (v : Fin A.places)
    (x y : (BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℂ) :
    DataTheta.standardPairing (ComplexIntrinsicAction.Coordinate.complexifiedLinear (realPlaceProjection A v) x) y =
      DataTheta.standardPairing x (ComplexIntrinsicAction.Coordinate.complexifiedLinear (realPlaceProjection A v) y) := by
  rw [← ComplexSymplecticPairing.complexPhaseCoordinates_pairing A P, ← ComplexSymplecticPairing.complexPhaseCoordinates_pairing A P,
    complex_place_projection, complex_place_projection, geometric_projection_pairing]

theorem projection_preserves_hodge (v : Fin A.places) (z : BallNatural.Ball) (x : BallGeometryData.ComplexPhase A)
    (hx : x ∈ BallGeometryData.HodgeSubspace A z) : geometricPlaceProjection A v x ∈ BallGeometryData.HodgeSubspace A z := by
  obtain ⟨a, rfl⟩ := hx
  rw [geometric_frame_projection]
  exact ⟨framePlaceProjection A v a, rfl⟩

theorem projection_preserves_period_graph (v : Fin A.places) (z : BallNatural.Ball)
    (q : BallGeometryData.FrameIndex A → ℂ) :
    ∃ q' : BallGeometryData.FrameIndex A → ℂ,
      ComplexIntrinsicAction.Coordinate.complexifiedLinear (realPlaceProjection A v)
        (Sum.elim q ((PeriodCoordinates.geometricPeriod A P z).matrix.mulVec q)) =
          Sum.elim q' ((PeriodCoordinates.geometricPeriod A P z).matrix.mulVec q') := by
  have hx : ComplexPhaseCoordinates.complexPhaseCoordinates A P
      (Sum.elim q ((PeriodCoordinates.geometricPeriod A P z).matrix.mulVec q)) ∈ BallGeometryData.HodgeSubspace A z :=
    (PeriodCoordinates.geometric_period_range A P z _).mpr ⟨q, rfl⟩
  have hp := projection_preserves_hodge A v z _ hx
  rw [← complex_place_projection] at hp
  obtain ⟨q', hq'⟩ := (PeriodCoordinates.geometric_period_range A P z _).mp hp
  exact ⟨q', ((ComplexPhaseCoordinates.complexPhaseCoordinates A P).injective hq').symm⟩

end

end OAI.RepresentationTheory.Theta.Adelic.PeriodPlaceProjection
