import OAI.ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice
import OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicPeriodBases

/-! # Holomorphic Chart Period Bases -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicChartPeriodBases

noncomputable section

/-! Open continuous full markings from actual chart exponentials. -/

open scoped Classical _root_.Manifold ContDiff _root_.Topology

open OAI.ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice.Abelian

theorem exists_holomorphic_full_chart_period_bases_on
    {P V X : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
    (L H : P → Type)
    [∀ p, NormedAddCommGroup (L p)] [∀ p, NormedSpace ℝ (L p)]
    [∀ p, FiniteDimensional ℝ (L p)] [∀ p, CompleteSpace (L p)]
    [∀ p, TopologicalSpace (H p)] [∀ p, ChartedSpace (L p) (H p)] [∀ p, CommGroup (H p)]
    [∀ p, LieGroup (𝓘(ℝ, L p)) ∞ (H p)] [∀ p, T2Space (H p)]
    (p₀ : P) [CompactSpace (H p₀)] [ConnectedSpace (H p₀)]
    (c : ∀ p, OpenPartialHomeomorph (H p) V)
    (embed : ∀ p, H p → X)
    (D : ArithmeticGeometry.Descent.CMVariety.LocalPeriod.Abelian.LocalPeriodFamily H (fun p => ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L p) (c p)) embed p₀)
    (hcontinue : ∀ v : V, ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L p₀) (c p₀) v = 1 →
      ∃ (U : Set P) (period : P → V), IsOpen U ∧ p₀ ∈ U ∧
        DifferentiableOn ℂ period U ∧ period p₀ = v ∧
          ∀ p ∈ U, ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L p) (c p) (period p) = 1)
    (hc : (c p₀).MDifferentiable (𝓘(ℝ, L p₀)) (𝓘(ℝ, V)))
    (h1 : (1 : H p₀) ∈ (c p₀).source) (h0 : c p₀ 1 = 0)
    (K : Set X) (hK : IsClosed K)
    (hmem : ∀ p v, embed p (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L p) (c p) v) ∈ K ↔
      ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L p) (c p) v = 1) :
    ∃ (n : ℕ) (r : P → (Fin n → ℝ) ≃L[ℝ] V) (U : Set P),
      IsOpen U ∧ p₀ ∈ U ∧ ContinuousOn (fun p => (r p).toContinuousLinearMap) U ∧
      (∀ i, DifferentiableOn ℂ (fun p => r p (Pi.single i 1)) U) ∧
      ∀ p ∈ U, ∃ b : Module.Basis (Fin n) ℤ (ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice.Abelian.chartPeriodLattice (E := L p) (c p)),
        ∀ i, (b i : V) = r p (Pi.single i 1) := by
  obtain ⟨n, b₀, r₀, hb₀⟩ := ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice.Abelian.exists_chart_period_basis (E := L p₀) (c p₀) hc h1 h0
  obtain ⟨U, r, hU, hpU, _, hr, hhol, hb⟩ := HolomorphicPeriodBases.exists_holomorphic_full_period_bases_on D hcontinue
    (fun p => ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice.Abelian.chartPeriodLattice (E := L p) (c p))
    (fun p => ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice.Abelian.mem_chartPeriodLattice (E := L p) (c p)) K hK hmem b₀ r₀ (by
      intro i
      apply (hb₀ i).trans
      apply congrArg r₀
      funext j
      simp [Pi.single_apply])
  refine ⟨n, r, U, hU, hpU, hr, ?_, ?_⟩
  · intro i
    apply (hhol i).congr
    intro p _
    apply congrArg (r p)
    funext j
    simp [Pi.single_apply]
  · intro p hp
    obtain ⟨bp, hbp⟩ := hb p hp
    refine ⟨bp, fun i => (hbp i).trans ?_⟩
    apply congrArg (r p)
    funext j
    simp [Pi.single_apply]

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicChartPeriodBases
