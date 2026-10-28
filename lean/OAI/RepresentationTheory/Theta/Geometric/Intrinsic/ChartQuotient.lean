import OAI.ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice

/-! # Chart Quotient -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.ChartQuotient

noncomputable section

/-! The quotient by the actual chart-period lattice is the original
connected native group, through its own exponential map. -/

open scoped _root_.Manifold ContDiff

open OAI.ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice.Abelian

variable {E V G : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace G] [ChartedSpace E G] [CommGroup G]
    [LieGroup (𝓘(ℝ, E)) ∞ G] [T2Space G] [ConnectedSpace G]
    (c : OpenPartialHomeomorph G V)
    (hc : c.MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, V))) (h1 : (1 : G) ∈ c.source) (h0 : c 1 = 0)

def nativeChartQuotientHomeomorph : (V ⧸ (ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice.Abelian.chartPeriodLattice (E := E) c).toAddSubgroup) ≃ₜ G := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup (𝓘(ℝ, E)) ∞
  let T := ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice.Abelian.chartTangentEquiv c hc h1 h0
  let p : V →+ Additive G := (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialLocal.Constructions.Exponential.expAddHom (E := E) (C := G)).comp T.toLinearEquiv.toAddMonoidHom
  have hp : IsLocalHomeomorph p :=
    (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialLocal.Constructions.Exponential.expMap_isLocalHomeomorph (E := E) (C := G)).comp T.toHomeomorph.isLocalHomeomorph
  have hs : Function.Surjective p := (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialLocal.Constructions.Exponential.expMap_surjective (E := E) (C := G)).comp T.surjective
  exact AlgebraicGeometry.HodgeConjecture.DegreeTwo.UniformizationEq.Constructions.Uniformization.quotientHomeomorph p hp hs

theorem nativeChartQuotientHomeomorph_mk (v : V) :
    nativeChartQuotientHomeomorph c hc h1 h0 (QuotientAddGroup.mk v) =
      ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := E) c v := rfl

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.ChartQuotient
