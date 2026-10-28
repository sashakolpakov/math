import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource
import OAI.RepresentationTheory.Theta.Geometric.Period.Ne
import Mathlib.LinearAlgebra.Determinant

/-! # Linear Unitary Representative -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LinearUnitaryRepresentative.CM

noncomputable section

/-! A literal determinant-one Hermitian linear automorphism gives the
same rational SU matrix and the same fractional action on the ball. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.RepresentationTheory.Theta.Geometric.Period.Ne

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]

def specialLinear (g : GeometricSource.CM.Vec E ≃ₗ[E] GeometricSource.CM.Vec E) (hdet : LinearMap.det g.toLinearMap = 1) :
    Matrix.SpecialLinearGroup (Fin 3) E :=
  ⟨LinearMap.toMatrix' g.toLinearMap, (LinearMap.det_toMatrix' g.toLinearMap).trans hdet⟩

omit [NumberField E] [NumberField.IsCMField E] in
theorem specialLinear_linear (g : GeometricSource.CM.Vec E ≃ₗ[E] GeometricSource.CM.Vec E) (hdet : LinearMap.det g.toLinearMap = 1) :
    Matrix.SpecialLinearGroup.toLin' (specialLinear E g hdet) = g :=
  LinearEquiv.toLinearMap_injective (Matrix.toLin'_toMatrix' g.toLinearMap)

def rational (b : E) (g : GeometricSource.CM.Vec E ≃ₗ[E] GeometricSource.CM.Vec E)
    (hu : ∀ x y, GeometricSource.CM.hermitian E b (g x) (g y) = GeometricSource.CM.hermitian E b x y)
    (hdet : LinearMap.det g.toLinearMap = 1) : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU b := by
  refine ⟨specialLinear E g hdet, ?_⟩
  change ∀ x y, GeometricSource.CM.hermitian E b (Matrix.SpecialLinearGroup.toLin' (specialLinear E g hdet) x)
    (Matrix.SpecialLinearGroup.toLin' (specialLinear E g hdet) y) = GeometricSource.CM.hermitian E b x y
  rw [specialLinear_linear]
  exact hu

theorem rational_linear (b : E) (g : GeometricSource.CM.Vec E ≃ₗ[E] GeometricSource.CM.Vec E)
    (hu : ∀ x y, GeometricSource.CM.hermitian E b (g x) (g y) = GeometricSource.CM.hermitian E b x y)
    (hdet : LinearMap.det g.toLinearMap = 1) :
    Matrix.SpecialLinearGroup.toLin' (rational E b g hu hdet).val = g :=
  specialLinear_linear E g hdet

theorem period (b : E) (g : GeometricSource.CM.Vec E ≃ₗ[E] GeometricSource.CM.Vec E)
    (hu : ∀ x y, GeometricSource.CM.hermitian E b (g x) (g y) = GeometricSource.CM.hermitian E b x y)
    (hdet : LinearMap.det g.toLinearMap = 1) (z : GeometricSource.CM.BallChart)
    (hz : z ∈ Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (E.val b)) :
    RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm b E.val.toRingHom (rational E b g hu hdet) z = GeometricSource.CM.BallDatum.lineAction g z := by
  rw [RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm_eq_fractional b E.val.toRingHom _ z hz]
  funext i
  change RepresentationTheory.Theta.Geometric.Period.Ne.periodRow b E.val.toRingHom (rational E b g hu hdet) i.castSucc z /
    RepresentationTheory.Theta.Geometric.Period.Ne.periodRow b E.val.toRingHom (rational E b g hu hdet) 2 z = _
  rw [RepresentationTheory.Theta.Geometric.Period.Ne.periodRow_eq_mulVec, RepresentationTheory.Theta.Geometric.Period.Ne.periodRow_eq_mulVec]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LinearUnitaryRepresentative.CM
