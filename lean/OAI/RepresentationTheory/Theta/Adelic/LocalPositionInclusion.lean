import OAI.RepresentationTheory.Theta.Adelic.SiegelRestriction

/-! # Local Position Inclusion -/

namespace OAI.RepresentationTheory.Theta.Adelic.LocalPositionInclusion

noncomputable section

/-! The actual real position map at each archimedean place, embedded in
the global rationally normalized position coordinates. -/

open scoped Classical _root_.NumberField

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.MinkowskiCoordinatesPosition
open OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates OAI.RepresentationTheory.Theta.Adelic.SiegelRestriction

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

def localPositionInclusion (v : Fin A.places) : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m) →ₗ[ℝ] BallGeometryData.RealPositions A :=
  LinearMap.single ℝ (fun _ : Fin A.places => Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m)) v

def realPositionColumn (v : Fin A.places) : Matrix (BallGeometryData.FrameIndex A) (Fin (3 * m)) ℝ :=
  LinearMap.toMatrix' ((MinkowskiCoordinatesPosition.realPositionCoordinates A).toLinearEquiv.toLinearMap.comp
    (localPositionInclusion A v))

theorem realPositionColumn_apply (v : Fin A.places) (x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m)) :
    (realPositionColumn A v).mulVec x = MinkowskiCoordinatesPosition.realPositionCoordinates A (Pi.single v x) :=
  LinearMap.toMatrix'_mulVec _ x

theorem realPositionColumn_injective (v : Fin A.places) :
    Function.Injective (realPositionColumn A v).mulVec := by
  intro x y h
  rw [realPositionColumn_apply, realPositionColumn_apply] at h
  have he := (MinkowskiCoordinatesPosition.realPositionCoordinates A).injective h
  simpa only [Pi.single_eq_same] using congrFun he v

def localSiegelPeriod (v : Fin A.places) (z : BallNatural.Ball) : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin (3 * m)) :=
  SiegelRestriction.restrictedSiegel (PeriodCoordinates.geometricPeriod A P z) (realPositionColumn A v) (realPositionColumn_injective A v)

def localJacobiParameter (v : Fin A.places) (ξ : BallGeometryData.FrameIndex A → ℂ) : Fin (3 * m) → ℂ :=
  ((realPositionColumn A v).map Complex.ofRealHom).transpose.mulVec ξ

end

end OAI.RepresentationTheory.Theta.Adelic.LocalPositionInclusion
