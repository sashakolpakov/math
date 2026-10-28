import OAI.RepresentationTheory.Theta.Adelic.MomentumCoordinates
import OAI.RepresentationTheory.Theta.Adelic.DataTheta

/-! # Phase Coordinates -/

namespace OAI.RepresentationTheory.Theta.Adelic.PhaseCoordinates

noncomputable section

/-! Actual rational and real symplectic phase coordinates, with the
specified position part and exact principal-vector compatibility. -/

open scoped Classical _root_.NumberField

open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition
open OAI.RepresentationTheory.Theta.Adelic.MomentumCoordinates OAI.RepresentationTheory.Theta.Adelic.MomentumCoordinates.PositionPairing

theorem native_coordinatePairing_sum {k : Type*} [Field k] (n m : ℕ)
    (x y : (Fin (n * m) ⊕ Fin (n * m)) → k) :
    Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing n m x y =
      (∑ j, x (.inl j) * y (.inr j)) - (∑ j, x (.inr j) * y (.inl j)) := by
  simp [Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing, Matrix.J, Matrix.toBilin'_apply,
    Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]
  ring

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

def rationalPhaseCoordinates :
    Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace F (3 * m) ≃ₗ[ℚ] ((BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℚ) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin (3 * m)) (Fin (3 * m)) ℚ F).trans
    (((MinkowskiCoordinatesPosition.rationalPositionCoordinates A).prodCongr (MomentumCoordinates.rationalMomentumCoordinates A)).trans
      (LinearEquiv.sumArrowLequivProdArrow (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℚ ℚ).symm)

def splitRealPhase :
    (Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m)) ≃ₗ[ℝ] (BallGeometryData.RealPositions A × BallGeometryData.RealPositions A) where
  toFun x := (fun v j => x v (.inl j), fun v j => x v (.inr j))
  invFun x v := Sum.elim (x.1 v) (x.2 v)
  left_inv x := by funext v i; cases i <;> rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def realPhaseCoordinates :
    (Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m)) ≃L[ℝ] ((BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv ((splitRealPhase A).trans
    ((((MinkowskiCoordinatesPosition.realPositionCoordinates A).toLinearEquiv).prodCongr
      (MomentumCoordinates.realMomentumCoordinates A).toLinearEquiv).trans
        (LinearEquiv.sumArrowLequivProdArrow (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℝ ℝ).symm))

theorem rationalPhaseCoordinates_inl (x : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace F (3 * m)) (i : BallGeometryData.FrameIndex A) :
    rationalPhaseCoordinates A x (.inl i) =
      MinkowskiCoordinatesPosition.rationalPositionCoordinates A (fun j => x (.inl j)) i := rfl

theorem rationalPhaseCoordinates_inr (x : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace F (3 * m)) (i : BallGeometryData.FrameIndex A) :
    rationalPhaseCoordinates A x (.inr i) =
      MomentumCoordinates.rationalMomentumCoordinates A (fun j => x (.inr j)) i := rfl

theorem realPhaseCoordinates_inl (x : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m)) (i : BallGeometryData.FrameIndex A) :
    realPhaseCoordinates A x (.inl i) =
      MinkowskiCoordinatesPosition.realPositionCoordinates A (fun v j => x v (.inl j)) i := rfl

theorem realPhaseCoordinates_inr (x : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m)) (i : BallGeometryData.FrameIndex A) :
    realPhaseCoordinates A x (.inr i) =
      MomentumCoordinates.realMomentumCoordinates A (fun v j => x v (.inr j)) i := rfl

theorem realPhaseCoordinates_rational (x : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace F (3 * m))
    (i : BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) :
    realPhaseCoordinates A (fun v j =>
      A.real v (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl (A.enumerate v)) (x j))) i =
        (rationalPhaseCoordinates A x i : ℝ) := by
  cases i with
  | inl i => exact MinkowskiCoordinatesPosition.realPositionCoordinates_rational A _ i
  | inr i => exact MomentumCoordinates.realMomentumCoordinates_rational A _ i

theorem rationalPhaseCoordinates_pairing (x y : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace F (3 * m)) :
    DataTheta.standardPairing (rationalPhaseCoordinates A x) (rationalPhaseCoordinates A y) =
      Algebra.trace ℚ F (Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing 3 m x y) := by
  simp only [DataTheta.standardPairing, rationalPhaseCoordinates_inl, rationalPhaseCoordinates_inr,
    Finset.sum_sub_distrib]
  rw [show (∑ i, MomentumCoordinates.rationalMomentumCoordinates A (fun j => x (.inr j)) i *
      MinkowskiCoordinatesPosition.rationalPositionCoordinates A (fun j => y (.inl j)) i) =
    ∑ i, MinkowskiCoordinatesPosition.rationalPositionCoordinates A (fun j => y (.inl j)) i *
      MomentumCoordinates.rationalMomentumCoordinates A (fun j => x (.inr j)) i from
        Finset.sum_congr rfl (fun _ _ => mul_comm _ _)]
  rw [MomentumCoordinates.PositionPairing.rational_position_momentum_pairing, MomentumCoordinates.PositionPairing.rational_position_momentum_pairing, ← map_sub]
  congr 1
  rw [native_coordinatePairing_sum]
  congr 1
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem realPhaseCoordinates_pairing (x y : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ (3 * m)) :
    DataTheta.standardPairing (realPhaseCoordinates A x) (realPhaseCoordinates A y) =
      ∑ v, DataTheta.standardPairing (x v) (y v) := by
  simp only [DataTheta.standardPairing, realPhaseCoordinates_inl, realPhaseCoordinates_inr,
    Finset.sum_sub_distrib]
  rw [show (∑ i, MomentumCoordinates.realMomentumCoordinates A (fun v j => x v (.inr j)) i *
      MinkowskiCoordinatesPosition.realPositionCoordinates A (fun v j => y v (.inl j)) i) =
    ∑ i, MinkowskiCoordinatesPosition.realPositionCoordinates A (fun v j => y v (.inl j)) i *
      MomentumCoordinates.realMomentumCoordinates A (fun v j => x v (.inr j)) i from
        Finset.sum_congr rfl (fun _ _ => mul_comm _ _)]
  rw [MomentumCoordinates.PositionPairing.real_position_momentum_pairing, MomentumCoordinates.PositionPairing.real_position_momentum_pairing]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

end

end OAI.RepresentationTheory.Theta.Adelic.PhaseCoordinates
