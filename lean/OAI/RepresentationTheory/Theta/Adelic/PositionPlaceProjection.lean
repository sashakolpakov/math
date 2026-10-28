import OAI.RepresentationTheory.Theta.Adelic.PeriodPlaceProjection
import OAI.RepresentationTheory.Theta.Adelic.LocalPositionInclusion

/-! # Position Place Projection -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Adelic.PositionPlaceProjection

/-! The position part of the actual place projection depends only on
position coordinates, and is the projection through the real Minkowski
position map. Its complexification has the same block property. -/

open scoped Classical _root_.NumberField

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.PhaseCoordinates OAI.RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition
open OAI.RepresentationTheory.Theta.Adelic.ComplexIntrinsicAction.Coordinate OAI.RepresentationTheory.Theta.Adelic.PeriodPlaceProjection OAI.RepresentationTheory.Theta.Adelic.LocalPositionInclusion

def positionPart {R I : Type} [Semiring R] : ((I ⊕ I) → R) →ₗ[R] (I → R) :=
  LinearMap.pi (fun i => LinearMap.proj (.inl i))

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

def positionPlaceProjection (v : Fin A.places) : (BallGeometryData.FrameIndex A → ℝ) →ₗ[ℝ] (BallGeometryData.FrameIndex A → ℝ) :=
  LinearMap.comp (MinkowskiCoordinatesPosition.realPositionCoordinates A).toLinearEquiv.toLinearMap
    (LinearMap.comp (PeriodPlaceProjection.placeProjection (R := ℝ) v) (MinkowskiCoordinatesPosition.realPositionCoordinates A).symm.toLinearEquiv.toLinearMap)

theorem positionPlaceProjection_native (v : Fin A.places) (x : BallGeometryData.RealPositions A) :
    positionPlaceProjection A v (MinkowskiCoordinatesPosition.realPositionCoordinates A x) =
      MinkowskiCoordinatesPosition.realPositionCoordinates A (Pi.single v (x v)) := by
  change MinkowskiCoordinatesPosition.realPositionCoordinates A (PeriodPlaceProjection.placeProjection v
    ((MinkowskiCoordinatesPosition.realPositionCoordinates A).symm (MinkowskiCoordinatesPosition.realPositionCoordinates A x))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

theorem realPlaceProjection_position (v : Fin A.places)
    (x : (BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℝ) :
    positionPart (PeriodPlaceProjection.realPlaceProjection A v x) = positionPlaceProjection A v (positionPart x) := by
  obtain ⟨u, rfl⟩ := (PhaseCoordinates.realPhaseCoordinates A).surjective x
  rw [PeriodPlaceProjection.realPlaceProjection_native]
  have hpos (y : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m)) :
      positionPart (PhaseCoordinates.realPhaseCoordinates A y) = MinkowskiCoordinatesPosition.realPositionCoordinates A (fun w j => y w (.inl j)) := rfl
  rw [hpos, hpos, positionPlaceProjection_native]
  apply congrArg (MinkowskiCoordinatesPosition.realPositionCoordinates A)
  funext w j
  by_cases hw : w = v
  · subst w
    simp
  · simp [hw]

theorem complexPlaceProjection_position (v : Fin A.places)
    (x : (BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℂ) :
    positionPart (ComplexIntrinsicAction.Coordinate.complexifiedLinear (PeriodPlaceProjection.realPlaceProjection A v) x) =
      ComplexIntrinsicAction.Coordinate.complexifiedLinear (positionPlaceProjection A v) (positionPart x) := by
  have h : (positionPart (R := ℂ)).comp (ComplexIntrinsicAction.Coordinate.complexifiedLinear (PeriodPlaceProjection.realPlaceProjection A v)) =
      (ComplexIntrinsicAction.Coordinate.complexifiedLinear (positionPlaceProjection A v)).comp positionPart := by
    apply ComplexIntrinsicAction.Coordinate.complexLinear_ext_real
    intro u
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ComplexIntrinsicAction.Coordinate.complexifiedLinear_real]
    have hp : positionPart (fun i => (u i : ℂ)) = fun i => ((positionPart u i : ℝ) : ℂ) := rfl
    rw [hp, ComplexIntrinsicAction.Coordinate.complexifiedLinear_real]
    exact congrArg (fun q => fun i => (q i : ℂ)) (realPlaceProjection_position A v u)
  exact LinearMap.congr_fun h x

theorem positionProjection_column_same (v : Fin A.places) (x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m)) :
    positionPlaceProjection A v ((LocalPositionInclusion.realPositionColumn A v).mulVec x) =
      (LocalPositionInclusion.realPositionColumn A v).mulVec x := by
  rw [LocalPositionInclusion.realPositionColumn_apply, positionPlaceProjection_native, Pi.single_eq_same]

theorem positionProjection_column_ne (v w : Fin A.places) (hvw : v ≠ w) (x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m)) :
    positionPlaceProjection A v ((LocalPositionInclusion.realPositionColumn A w).mulVec x) = 0 := by
  rw [LocalPositionInclusion.realPositionColumn_apply, positionPlaceProjection_native]
  simp [hvw]

theorem complexPositionProjection_column_ne (v w : Fin A.places) (hvw : v ≠ w)
    (x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m)) :
    ComplexIntrinsicAction.Coordinate.complexifiedLinear (positionPlaceProjection A v)
      (fun i => ((LocalPositionInclusion.realPositionColumn A w).mulVec x i : ℂ)) = 0 := by
  rw [ComplexIntrinsicAction.Coordinate.complexifiedLinear_real, positionProjection_column_ne A v w hvw]
  simp
  rfl

end RepresentationTheory.Theta.Adelic.PositionPlaceProjection

namespace RepresentationTheory.Theta.Adelic.PositionPlaceProjection.Pure

/-! A pure position vector from a single place is fixed by that place's
real and complex phase projections. -/

open scoped Classical _root_.NumberField

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.PhaseCoordinates OAI.RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition OAI.RepresentationTheory.Theta.Adelic.MomentumCoordinates
open OAI.RepresentationTheory.Theta.Adelic.ComplexIntrinsicAction.Coordinate OAI.RepresentationTheory.Theta.Adelic.PeriodPlaceProjection OAI.RepresentationTheory.Theta.Adelic.LocalPositionInclusion

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

theorem realPhaseCoordinates_pure_position (v : Fin A.places) (x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m)) :
    PhaseCoordinates.realPhaseCoordinates A (Pi.single v (Sum.elim x 0)) =
      Sum.elim ((LocalPositionInclusion.realPositionColumn A v).mulVec x) 0 := by
  have hq : (fun (w : Fin A.places) (j : Fin (3 * m)) =>
      (Pi.single v (Sum.elim x 0) : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m)) w (.inl j)) = Pi.single v x := by
    funext w j
    by_cases hw : w = v
    · subst w
      simp
    · simp [hw]
  have hp : (fun (w : Fin A.places) (j : Fin (3 * m)) =>
      (Pi.single v (Sum.elim x 0) : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m)) w (.inr j)) = (0 : BallGeometryData.RealPositions A) := by
    funext w j
    by_cases hw : w = v
    · subst w
      simp
    · simp [hw]
  funext i
  cases i with
  | inl i =>
    rw [PhaseCoordinates.realPhaseCoordinates_inl, hq, LocalPositionInclusion.realPositionColumn_apply]
    rfl
  | inr i =>
    rw [PhaseCoordinates.realPhaseCoordinates_inr, hp, map_zero]
    rfl

theorem realPlaceProjection_pure_position (v : Fin A.places) (x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m)) :
    PeriodPlaceProjection.realPlaceProjection A v (Sum.elim ((LocalPositionInclusion.realPositionColumn A v).mulVec x) 0) =
      Sum.elim ((LocalPositionInclusion.realPositionColumn A v).mulVec x) 0 := by
  rw [← realPhaseCoordinates_pure_position, PeriodPlaceProjection.realPlaceProjection_native, Pi.single_eq_same]

theorem complexPlaceProjection_pure_position (v : Fin A.places) (x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m)) :
    ComplexIntrinsicAction.Coordinate.complexifiedLinear (PeriodPlaceProjection.realPlaceProjection A v)
      (Sum.elim (fun i => ((LocalPositionInclusion.realPositionColumn A v).mulVec x i : ℂ)) 0) =
        Sum.elim (fun i => ((LocalPositionInclusion.realPositionColumn A v).mulVec x i : ℂ)) 0 := by
  have hcast : (fun i : BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A =>
      ((Sum.elim ((LocalPositionInclusion.realPositionColumn A v).mulVec x) 0 i : ℝ) : ℂ)) =
      Sum.elim (fun i => ((LocalPositionInclusion.realPositionColumn A v).mulVec x i : ℂ)) 0 := by
    funext i
    cases i <;> rfl
  rw [← hcast, ComplexIntrinsicAction.Coordinate.complexifiedLinear_real, realPlaceProjection_pure_position]

end RepresentationTheory.Theta.Adelic.PositionPlaceProjection.Pure

end

end OAI
