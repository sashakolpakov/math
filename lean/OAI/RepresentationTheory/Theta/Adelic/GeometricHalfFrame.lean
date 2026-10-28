import OAI.RepresentationTheory.Theta.Adelic.PeriodHolomorphic
import OAI.RepresentationTheory.Theta.Adelic.BallHolomorphicSquare

/-! # Geometric Half Frame -/

namespace OAI.RepresentationTheory.Theta.Adelic.GeometricHalfFrame

noncomputable section

/-! The holomorphic half-determinant frame is constructed from the
determinant of the actual period-frame position matrix. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural
open OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates OAI.RepresentationTheory.Theta.Adelic.PeriodHolomorphic OAI.RepresentationTheory.Theta.Adelic.BallHolomorphicSquare.Root

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

theorem position_determinant_holomorphic :
    BallGeometryData.BallHolomorphic (fun z => (PeriodCoordinates.geometricPositionUnit A P z).val.det) := by
  have h := AlgebraicGeometry.HodgeConjecture.ThetaCycle.MatrixCalculus.CM.matrix_determinant_holomorphic (PeriodHolomorphic.rawHodgePosition A P)
    (PeriodHolomorphic.rawHodgePosition_holomorphic A P).differentiableOn (s := BallGeometryData.ballDomain)
  apply h.congr
  intro z hz
  rw [dite_eq_left hz]
  rfl

theorem exists_geometricHalfFrame : ∃ h : BallNatural.Ball → ℂ, BallGeometryData.BallHolomorphic h ∧
    ∀ z, h z ≠ 0 ∧ h z ^ 2 = (PeriodCoordinates.geometricPositionUnit A P z).val.det :=
  BallHolomorphicSquare.Root.ball_holomorphic_square_root _ (position_determinant_holomorphic A P)
    (PeriodCoordinates.hodgePosition_det_ne_zero A P)

def geometricHalfFrame : BallNatural.Ball → ℂ := (exists_geometricHalfFrame A P).choose

theorem geometricHalfFrame_holomorphic : BallGeometryData.BallHolomorphic (geometricHalfFrame A P) :=
  (exists_geometricHalfFrame A P).choose_spec.1

theorem geometricHalfFrame_nonzero (z : BallNatural.Ball) : geometricHalfFrame A P z ≠ 0 :=
  ((exists_geometricHalfFrame A P).choose_spec.2 z).1

theorem geometricHalfFrame_square (z : BallNatural.Ball) :
    geometricHalfFrame A P z ^ 2 = (PeriodCoordinates.geometricPositionUnit A P z).val.det :=
  ((exists_geometricHalfFrame A P).choose_spec.2 z).2

end

end OAI.RepresentationTheory.Theta.Adelic.GeometricHalfFrame
