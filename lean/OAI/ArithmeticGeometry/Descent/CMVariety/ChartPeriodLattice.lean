import OAI.ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialLocal
import Mathlib.Algebra.Module.ZLattice.Basic

/-! # Chart Period Lattice -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice.Abelian

noncomputable section

/-!
The period lattice in the constructed chart tangent coordinates is the
actual native exponential lattice pulled back by the inverse-chart
derivative. A differentiable identity chart makes that derivative a real
linear isomorphism, so the chart lattice has a full integral basis.
-/

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialLocal.Constructions.Exponential
open scoped _root_.Manifold ContDiff Classical

variable {E V G : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace G] [ChartedSpace E G] [CommGroup G]
  [LieGroup (𝓘(ℝ, E)) ∞ G] [T2Space G]

def chartPeriodLattice (c : OpenPartialHomeomorph G V) : Submodule ℤ V :=
  ZLattice.comap ℝ (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialLocal.Constructions.Exponential.expLattice (E := E) (C := G)) (ChartEndomorphismDerivative.Abelian.chartTangentMap (E := E) c).toLinearMap

omit [FiniteDimensional ℝ E] in
theorem mem_chartPeriodLattice (c : OpenPartialHomeomorph G V) (v : V) :
    v ∈ chartPeriodLattice (E := E) c ↔ ChartEndomorphismDerivative.Abelian.chartExponential (E := E) c v = 1 := Iff.rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [LieGroup (𝓘(ℝ, E)) ∞ G] [T2Space G] in
def chartTangentEquiv
    (c : OpenPartialHomeomorph G V) (hc : c.MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, V)))
    (h1 : (1 : G) ∈ c.source) (h0 : c 1 = 0) : V ≃L[ℝ] E :=
  hc.symm.mfderiv (h0 ▸ c.map_source h1)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [LieGroup (𝓘(ℝ, E)) ∞ G] [T2Space G] in
theorem chartTangentEquiv_toContinuousLinearMap
    (c : OpenPartialHomeomorph G V) (hc : c.MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, V)))
    (h1 : (1 : G) ∈ c.source) (h0 : c 1 = 0) :
    (chartTangentEquiv c hc h1 h0).toContinuousLinearMap = ChartEndomorphismDerivative.Abelian.chartTangentMap (E := E) c := rfl

/-- Compactness and connectedness of the actual native fiber supply the
central full integral lattice basis in its inverse-chart tangent coordinates. -/
theorem exists_chart_period_basis [CompactSpace G] [ConnectedSpace G]
    (c : OpenPartialHomeomorph G V) (hc : c.MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, V)))
    (h1 : (1 : G) ∈ c.source) (h0 : c 1 = 0) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℤ (chartPeriodLattice (E := E) c))
      (e : (Fin n → ℝ) ≃L[ℝ] V), ∀ i, (b i : V) = e (Pi.single i 1) := by
  let T := chartTangentEquiv c hc h1 h0
  let Λ := chartPeriodLattice (E := E) c
  let : FiniteDimensional ℝ V := FiniteDimensional.of_injective T.toLinearMap T.injective
  let : DiscreteTopology Λ := inferInstanceAs
    (DiscreteTopology (ZLattice.comap ℝ (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialLocal.Constructions.Exponential.expLattice (E := E) (C := G)) T.toLinearMap))
  let : IsZLattice ℝ Λ := inferInstanceAs
    (IsZLattice ℝ (ZLattice.comap ℝ (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialLocal.Constructions.Exponential.expLattice (E := E) (C := G)) T.toLinearMap))
  let b := Module.finBasis ℤ Λ
  let e := (b.ofZLatticeBasis ℝ Λ).equivFun.symm.toContinuousLinearEquiv
  refine ⟨Module.finrank ℤ Λ, b, e, ?_⟩
  intro i
  change (b i : V) = (b.ofZLatticeBasis ℝ Λ).equivFun.symm (Pi.single i 1)
  erw [Module.Basis.equivFun_symm_apply]
  simp [Pi.single_apply]

end

end OAI.ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice.Abelian
