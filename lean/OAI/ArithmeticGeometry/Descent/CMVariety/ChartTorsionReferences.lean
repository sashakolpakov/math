import OAI.ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice
import OAI.ArithmeticGeometry.Descent.CMVariety.TorsionPeriodCoordinates
import OAI.ArithmeticGeometry.Descent.CMVariety.LocalPeriod

/-! # Chart Torsion References -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety

noncomputable section

/-! Actual chart exponentials and continuous divided-period references. -/

open scoped _root_.Manifold ContDiff _root_.Topology

theorem ChartTorsionReferences.Abelian.chartExponential_surjective
    {E V G : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace G] [ChartedSpace E G] [CommGroup G]
    [LieGroup (𝓘(ℝ, E)) ∞ G] [T2Space G] [ConnectedSpace G]
    (c : OpenPartialHomeomorph G V)
    (hc : c.MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, V)))
    (h1 : (1 : G) ∈ c.source) (h0 : c 1 = 0) :
    Function.Surjective (ChartEndomorphismDerivative.Abelian.chartExponential (E := E) c) :=
  (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialLocal.Constructions.Exponential.expMap_surjective (E := E) (C := G)).comp (ChartPeriodLattice.Abelian.chartTangentEquiv c hc h1 h0).surjective

theorem LocalPeriod.Abelian.LocalPeriodFamily.continuousAt_divided_period
    {P V X Index : Type} [TopologicalSpace P] [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype Index]
    {G : P → Type} [∀ p, Group (G p)]
    {exponential : ∀ p, V → G p} {embed : ∀ p, G p → X} {p₀ : P}
    (H : LocalPeriod.Abelian.LocalPeriodFamily G exponential embed p₀)
    (r : P → (Index → ℝ) →L[ℝ] V) (hr : ContinuousAt r p₀)
    (n : ℕ) (z : Index → ℤ) :
    ContinuousAt (fun p => embed p
      (exponential p ((n : ℝ)⁻¹ • r p (fun i => (z i : ℝ))))) p₀ := by
  have hv : ContinuousAt (fun p => (n : ℝ)⁻¹ • r p (fun i => (z i : ℝ))) p₀ :=
    continuousAt_const.smul (hr.clm_apply continuousAt_const)
  exact (H.continuous _).comp
    (f := fun p => (p, (n : ℝ)⁻¹ • r p (fun i => (z i : ℝ))))
    (continuousAt_id.prodMk hv)

end

end OAI.ArithmeticGeometry.Descent.CMVariety
