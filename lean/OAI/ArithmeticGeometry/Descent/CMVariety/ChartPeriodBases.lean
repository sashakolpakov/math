import OAI.ArithmeticGeometry.Descent.CMVariety.ChartPeriodLattice
import OAI.ArithmeticGeometry.Descent.CMVariety.PeriodBases

/-! # Chart Period Bases -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety

noncomputable section

/-! Full chart-period bases from the constructed local exponential data. -/

open scoped Classical _root_.Manifold ContDiff _root_.Topology

theorem LocalPeriod.Abelian.LocalPeriodFamily.exists_full_chart_period_bases
    {P V X : Type} [TopologicalSpace P] [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L H : P → Type)
    [∀ p, NormedAddCommGroup (L p)] [∀ p, NormedSpace ℝ (L p)]
    [∀ p, FiniteDimensional ℝ (L p)] [∀ p, CompleteSpace (L p)]
    [∀ p, TopologicalSpace (H p)] [∀ p, ChartedSpace (L p) (H p)] [∀ p, CommGroup (H p)]
    [∀ p, LieGroup (𝓘(ℝ, L p)) ∞ (H p)] [∀ p, T2Space (H p)]
    (p₀ : P) [CompactSpace (H p₀)] [ConnectedSpace (H p₀)]
    (c : ∀ p, OpenPartialHomeomorph (H p) V)
    (embed : ∀ p, H p → X)
    (D : LocalPeriod.Abelian.LocalPeriodFamily H (fun p => ChartEndomorphismDerivative.Abelian.chartExponential (E := L p) (c p)) embed p₀)
    (hc : (c p₀).MDifferentiable (𝓘(ℝ, L p₀)) (𝓘(ℝ, V)))
    (h1 : (1 : H p₀) ∈ (c p₀).source) (h0 : c p₀ 1 = 0)
    (K : Set X) (hK : IsClosed K)
    (hmem : ∀ p v, embed p (ChartEndomorphismDerivative.Abelian.chartExponential (E := L p) (c p) v) ∈ K ↔
      ChartEndomorphismDerivative.Abelian.chartExponential (E := L p) (c p) v = 1) :
    ∃ (n : ℕ) (r : P → (Fin n → ℝ) ≃L[ℝ] V),
      ContinuousAt (fun p => (r p).toContinuousLinearMap) p₀ ∧
      ∀ᶠ p in 𝓝 p₀, ∃ b : Module.Basis (Fin n) ℤ (ChartPeriodLattice.Abelian.chartPeriodLattice (E := L p) (c p)),
        ∀ i, (b i : V) = r p (Pi.single i 1) := by
  obtain ⟨n, b₀, r₀, hb₀⟩ := ChartPeriodLattice.Abelian.exists_chart_period_basis (E := L p₀) (c p₀) hc h1 h0
  obtain ⟨r, _, hr, hb⟩ := D.exists_continuous_full_period_bases
    (fun p => ChartPeriodLattice.Abelian.chartPeriodLattice (E := L p) (c p))
    (fun p => ChartPeriodLattice.Abelian.mem_chartPeriodLattice (E := L p) (c p)) K hK hmem b₀ r₀ (by
      intro i
      apply (hb₀ i).trans
      apply congrArg r₀
      funext j
      simp [Pi.single_apply])
  refine ⟨n, r, hr, ?_⟩
  filter_upwards [hb] with p hp
  obtain ⟨bp, hbp⟩ := hp
  refine ⟨bp, fun i => (hbp i).trans ?_⟩
  apply congrArg (r p)
  funext j
  simp [Pi.single_apply]

end

end OAI.ArithmeticGeometry.Descent.CMVariety
