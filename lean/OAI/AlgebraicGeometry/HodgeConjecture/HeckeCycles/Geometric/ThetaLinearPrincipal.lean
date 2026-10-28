import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LinearUnitaryRepresentative
import OAI.RepresentationTheory.Theta.Geometric.PrincipalFiniteCoordinates

/-! # Theta Linear Principal -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaLinearPrincipal.CM

noncomputable section

/-! Original principal-level linear maps give actual rational elements
of the finite GeometricTheta subgroup, with unchanged period action. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LinearUnitaryRepresentative.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
  (g : GeometricSource.CM.Vec E ≃ₗ[E] GeometricSource.CM.Vec E)
  (hu : ∀ x y, GeometricSource.CM.hermitian E D.pel.reference.b (g x) (g y) = GeometricSource.CM.hermitian E D.pel.reference.b x y)
  (hdet : LinearMap.det g.toLinearMap = 1)

theorem linear : D.rationalLinear (LinearUnitaryRepresentative.CM.rational E D.pel.reference.b g hu hdet) = g :=
  LinearUnitaryRepresentative.CM.rational_linear E D.pel.reference.b g hu hdet

theorem member (hc : D.HasFiniteCoordinates)
    (hL : ∀ x, x ∈ D.pel.reference.lattice ↔ g x ∈ D.pel.reference.lattice)
    (hN : ∀ x ∈ D.pel.reference.lattice, ∃ y ∈ D.pel.reference.lattice,
      g x - x = D.pel.level • y) :
    D.rationalFinite (LinearUnitaryRepresentative.CM.rational E D.pel.reference.b g hu hdet) ∈
      (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.integralSL3 q).prod D.awayLevel.toSubgroup := by
  apply D.principal_finite_membership hc
  · simpa only [linear E D g hu hdet] using hL
  · simpa only [linear E D g hu hdet] using hN

theorem period (hμ : D.pel.reference.μ = E.val.toRingHom) (z : D.domain) :
    D.periodMap (LinearUnitaryRepresentative.CM.rational E D.pel.reference.b g hu hdet) z.val = GeometricSource.CM.BallDatum.lineAction g z.val := by
  have hz : z.val ∈ Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (E.val D.pel.reference.b) :=
    Eq.mp (congrArg (fun μ : E →+* ℂ => z.val ∈ Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (μ D.pel.reference.b)) hμ)
      z.property
  exact (congrArg (fun μ : E →+* ℂ =>
    RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm D.pel.reference.b μ (LinearUnitaryRepresentative.CM.rational E D.pel.reference.b g hu hdet) z.val) hμ).trans
    (LinearUnitaryRepresentative.CM.period E D.pel.reference.b g hu hdet z.val hz)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaLinearPrincipal.CM
