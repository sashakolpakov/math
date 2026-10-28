import OAI.RepresentationTheory.Theta.Adelic.PositiveGeometricPairing
import OAI.RepresentationTheory.Theta.Adelic.GeometricFrame
import OAI.RepresentationTheory.Hecke.RadialDilation.PositiveGraph

/-! # Period Coordinates -/

namespace OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates

noncomputable section

/-! The period matrix and invertible position frame are constructed
from the actual positive geometric Hodge frame. -/

open scoped Classical _root_.NumberField ComplexConjugate

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.GeometricFrame
open OAI.RepresentationTheory.Theta.Adelic.ComplexPhaseCoordinates OAI.RepresentationTheory.Theta.Adelic.ComplexSymplecticPairing OAI.RepresentationTheory.Theta.Adelic.GeometricConjugation
open OAI.RepresentationTheory.Theta.Adelic.GeometricTracePairing OAI.RepresentationTheory.Theta.Adelic.PositiveGeometricPairing

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

def coordinateHodgeLinear (z : BallNatural.Ball) :
    (BallGeometryData.FrameIndex A → ℂ) →ₗ[ℂ] ((BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) → ℂ) :=
  (ComplexPhaseCoordinates.complexPhaseCoordinates A P).symm.toLinearEquiv.toLinearMap.comp (GeometricFrame.geometricFrameLinear A z)

def coordinateHodgeMatrix (z : BallNatural.Ball) :
    Matrix (BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ :=
  LinearMap.toMatrix' (coordinateHodgeLinear A P z)

def hodgePosition (z : BallNatural.Ball) : Matrix (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ :=
  (coordinateHodgeMatrix A P z).submatrix Sum.inl id

def hodgeMomentum (z : BallNatural.Ball) : Matrix (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ :=
  (coordinateHodgeMatrix A P z).submatrix Sum.inr id

theorem complex_coordinate_frame (z : BallNatural.Ball) (a : BallGeometryData.FrameIndex A → ℂ) :
    ComplexPhaseCoordinates.complexPhaseCoordinates A P ((coordinateHodgeMatrix A P z).mulVec a) =
      BallGeometryData.geometricFrame A z a := by
  rw [coordinateHodgeMatrix, LinearMap.toMatrix'_mulVec]
  exact (ComplexPhaseCoordinates.complexPhaseCoordinates A P).apply_symm_apply _

theorem coordinate_frame_split (z : BallNatural.Ball) (a : BallGeometryData.FrameIndex A → ℂ) :
    ComplexPhaseCoordinates.complexPhaseCoordinates A P (Sum.elim ((hodgePosition A P z).mulVec a)
      ((hodgeMomentum A P z).mulVec a)) = BallGeometryData.geometricFrame A z a := by
  have he : Sum.elim ((hodgePosition A P z).mulVec a) ((hodgeMomentum A P z).mulVec a) =
      (coordinateHodgeMatrix A P z).mulVec a := by
    funext i
    cases i <;> rfl
  rw [he, complex_coordinate_frame]

theorem coordinate_frame_isotropic (z : BallNatural.Ball) :
    (hodgeMomentum A P z).transpose * hodgePosition A P z =
      (hodgePosition A P z).transpose * hodgeMomentum A P z := by
  apply Matrix.ext
  intro i j
  have h := (ComplexSymplecticPairing.complexPhaseCoordinates_pairing A P
    ((coordinateHodgeMatrix A P z).mulVec (Pi.single i 1))
    ((coordinateHodgeMatrix A P z).mulVec (Pi.single j 1))).symm
  rw [complex_coordinate_frame, complex_coordinate_frame, PositiveGeometricPairing.geometric_frame_isotropic] at h
  simp only [DataTheta.standardPairing, Matrix.mulVec_single_one, Matrix.col_apply,
    Finset.sum_sub_distrib] at h
  exact (sub_eq_zero.mp h).symm

theorem coordinate_frame_positive (z : BallNatural.Ball) (a : BallGeometryData.FrameIndex A → ℂ) (ha : a ≠ 0) :
    0 < (Hecke.RadialDilation.PositiveGraph.Realization.standardFramePairing ((hodgeMomentum A P z).mulVec a)
      ((hodgePosition A P z).mulVec a)).im := by
  have h := ComplexSymplecticPairing.complexPhaseCoordinates_pairing A P
    (fun i => conj ((coordinateHodgeMatrix A P z).mulVec a i))
    ((coordinateHodgeMatrix A P z).mulVec a)
  rw [GeometricConjugation.complexPhaseCoordinates_conjugate, complex_coordinate_frame] at h
  have hp := PositiveGeometricPairing.geometric_frame_positive A z a ha
  rw [h] at hp
  have he : DataTheta.standardPairing
      (fun i => conj ((coordinateHodgeMatrix A P z).mulVec a i))
      ((coordinateHodgeMatrix A P z).mulVec a) =
    Hecke.RadialDilation.PositiveGraph.Realization.standardFramePairing ((hodgeMomentum A P z).mulVec a)
      ((hodgePosition A P z).mulVec a) := by
    apply Finset.sum_congr rfl
    intro i _
    change conj ((hodgePosition A P z).mulVec a i) * (hodgeMomentum A P z).mulVec a i -
      conj ((hodgeMomentum A P z).mulVec a i) * (hodgePosition A P z).mulVec a i = _
    simp only [Complex.star_def]
    ring
  rwa [he] at hp

theorem hodgePosition_det_ne_zero (z : BallNatural.Ball) : (hodgePosition A P z).det ≠ 0 :=
  Hecke.RadialDilation.PositiveGraph.Realization.positive_frame_lower_det _ _ (coordinate_frame_positive A P z)

def geometricPeriod (z : BallNatural.Ball) : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (BallGeometryData.FrameIndex A) :=
  Hecke.RadialDilation.PositiveGraph.Realization.siegelOfPositiveFrame (hodgeMomentum A P z) (hodgePosition A P z)
    (coordinate_frame_isotropic A P z) (coordinate_frame_positive A P z)

def geometricPositionUnit (z : BallNatural.Ball) : (Matrix (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ)ˣ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (hodgePosition A P z) (hodgePosition_det_ne_zero A P z)

theorem geometricPeriod_frame (z : BallNatural.Ball) :
    (geometricPeriod A P z).matrix * hodgePosition A P z = hodgeMomentum A P z :=
  Hecke.RadialDilation.PositiveGraph.Realization.siegelOfPositiveFrame_columns _ _
    (coordinate_frame_isotropic A P z) (coordinate_frame_positive A P z)

theorem geometric_period_graph (z : BallNatural.Ball) (a : BallGeometryData.FrameIndex A → ℂ) :
    ComplexPhaseCoordinates.complexPhaseCoordinates A P
      (Sum.elim ((geometricPositionUnit A P z).val.mulVec a)
        ((geometricPeriod A P z).matrix.mulVec ((geometricPositionUnit A P z).val.mulVec a))) =
      BallGeometryData.geometricFrame A z a := by
  change ComplexPhaseCoordinates.complexPhaseCoordinates A P (Sum.elim ((hodgePosition A P z).mulVec a)
    ((geometricPeriod A P z).matrix.mulVec ((hodgePosition A P z).mulVec a))) = _
  rw [Matrix.mulVec_mulVec, geometricPeriod_frame, coordinate_frame_split]

theorem geometric_period_range (z : BallNatural.Ball) (w : BallGeometryData.ComplexPhase A) :
    w ∈ BallGeometryData.HodgeSubspace A z ↔ ∃ t : BallGeometryData.FrameIndex A → ℂ,
      ComplexPhaseCoordinates.complexPhaseCoordinates A P (Sum.elim t ((geometricPeriod A P z).matrix.mulVec t)) = w := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨(geometricPositionUnit A P z).val.mulVec a, geometric_period_graph A P z a⟩
  · rintro ⟨t, ht⟩
    let a := (geometricPositionUnit A P z).inv.mulVec t
    have hu : (geometricPositionUnit A P z).val.mulVec a = t := by
      rw [Matrix.mulVec_mulVec, (geometricPositionUnit A P z).val_inv, Matrix.one_mulVec]
    refine ⟨a, ?_⟩
    have hg := geometric_period_graph A P z a
    rw [hu] at hg
    exact hg.symm.trans ht

end

end OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates
