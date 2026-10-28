import OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicChartLogarithm
import OAI.ArithmeticGeometry.Descent.CMVariety.FamilyLogarithm

/-! # Constructed Holomorphic Logarithm -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ConstructedHolomorphicLogarithm

noncomputable section

section

/-! Construct a common holomorphic local logarithm of the actual chart
exponentials from joint continuity and analytic group multiplication. -/

open Set _root_.Metric
open scoped _root_.Topology _root_.Manifold ContDiff

open OAI.ArithmeticGeometry.Descent.CMVariety.FamilyLogarithm.Abelian

variable {P V : Type}
  [NormedAddCommGroup P] [NormedSpace ℂ P] [NormedSpace ℝ P]
  [IsScalarTower ℝ ℂ P] [FiniteDimensional ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V]
  (L G : P → Type)
  [∀ p, NormedAddCommGroup (L p)] [∀ p, NormedSpace ℝ (L p)]
  [∀ p, FiniteDimensional ℝ (L p)] [∀ p, CompleteSpace (L p)]
  [∀ p, TopologicalSpace (G p)] [∀ p, ChartedSpace (L p) (G p)]
  [∀ p, CommGroup (G p)] [∀ p, LieGroup (𝓘(ℝ, L p)) ∞ (G p)] [∀ p, T2Space (G p)]

theorem exists_constructed_holomorphic_chart_logarithm
    (c : ∀ p, OpenPartialHomeomorph (G p) V) (B : Set P)
    (hc : ∀ p ∈ B, (c p).MDifferentiable (𝓘(ℝ, L p)) (𝓘(ℝ, V)))
    (h1 : ∀ p ∈ B, (1 : G p) ∈ (c p).source) (h0 : ∀ p ∈ B, c p 1 = 0)
    (Ω : Set (P × V)) (hΩ : IsOpen Ω) (p₀ : P) (hp₀ : (p₀, (0 : V)) ∈ Ω)
    (hbase : ∀ q ∈ Ω, q.1 ∈ B)
    (hinside : ∀ q ∈ Ω, ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q.1) (c q.1) q.2 ∈ (c q.1).source)
    (hcont : ContinuousOn (fun q : P × V => c q.1
      (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q.1) (c q.1) q.2)) Ω)
    (m : P × (V × V) → V) (D : Set (P × (V × V))) (hD : IsOpen D)
    (hD₀ : (p₀, ((0 : V), 0)) ∈ D) (hm : ContDiffOn ℂ 3 m D)
    (hcomparison : ∀ p ∈ B, ∀ u v, (p, (u, v)) ∈ D →
      m (p, (u, v)) = c p ((c p).symm u * (c p).symm v)) :
    let f := fun q : P × V => c q.1 (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q.1) (c q.1) q.2)
    ∃ (U : Set P) (δ r : ℝ) (logarithm : P × V → V),
      IsOpen U ∧ p₀ ∈ U ∧ U ⊆ B ∧ 0 < δ ∧ 0 < r ∧ r ≤ δ / 2 ∧
      U ×ˢ closedBall (0 : V) δ ⊆ Ω ∧
      ContinuousOn logarithm (U ×ˢ closedBall (0 : V) (δ / 2)) ∧
      DifferentiableOn ℂ logarithm (U ×ˢ ball (0 : V) r) ∧
      (∀ p ∈ U, ∀ y ∈ closedBall (0 : V) (δ / 2),
        logarithm (p, y) ∈ closedBall (0 : V) δ ∧ f (p, logarithm (p, y)) = y) ∧
      ∀ p ∈ U, ∀ v ∈ closedBall (0 : V) δ,
        f (p, v) ∈ closedBall (0 : V) (δ / 2) → logarithm (p, f (p, v)) = v := by
  dsimp only
  let : CompleteSpace V := FiniteDimensional.complete ℂ V
  let f := fun q : P × V => c q.1 (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q.1) (c q.1) q.2)
  obtain ⟨W, δ, logarithm, hW, hpW, hδ, hinto, hlog, hright, hleft⟩ :=
    ArithmeticGeometry.Descent.CMVariety.FamilyLogarithm.Abelian.exists_continuous_chart_logarithm L G c B hc h1 h0 Ω hΩ p₀ hp₀ hbase hinside hcont
      m D hD hD₀ ((hm.restrict_scalars ℝ).of_le (by norm_num : (2 : ℕ∞ω) ≤ 3)) hcomparison
  have hWB : W ⊆ B := by
    intro p hp
    exact hbase (p, 0) (hinto ⟨hp, mem_closedBall_self hδ.le⟩)
  have hzero (p : P) (hp : p ∈ W) : logarithm (p, 0) = 0 := by
    have h := hleft p hp 0 (mem_closedBall_self hδ.le)
    have hfzero : f (p, 0) = 0 := by
      dsimp only [f]
      rw [ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential_zero, h0 p (hWB hp)]
    change f (p, 0) ∈ closedBall (0 : V) (δ / 2) → logarithm (p, f (p, 0)) = 0 at h
    rw [hfzero] at h
    exact h (mem_closedBall_self (half_pos hδ).le)
  obtain ⟨U, r, hU, hpU, hUW, hr, hrδ, hhol⟩ :=
    HolomorphicChartLogarithm.exists_holomorphic_chart_logarithm_neighborhood L G c W hW
      (fun p hp => hc p (hWB hp)) (fun p hp => h1 p (hWB hp)) (fun p hp => h0 p (hWB hp))
      m D hD hm (fun p hp => hcomparison p (hWB hp)) p₀ hpW hD₀
      (δ / 2) (half_pos hδ) logarithm
      (hlog.mono (prod_mono Subset.rfl ball_subset_closedBall))
      (by
        intro p hp y hy
        have hy' := hright p hp y (ball_subset_closedBall hy)
        exact ⟨hinside (p, logarithm (p, y)) (hinto ⟨hp, hy'.1⟩), hy'.2⟩)
      hzero
  exact ⟨U, δ, r, logarithm, hU, hpU, hUW.trans hWB, hδ, hr, hrδ,
    (prod_mono hUW Subset.rfl).trans hinto,
    hlog.mono (prod_mono hUW Subset.rfl), hhol,
    fun p hp => hright p (hUW hp), fun p hp => hleft p (hUW hp)⟩

end

/-! Construct a holomorphic logarithm in an actual total-space chart,
retaining the native exponential, both inverse equations, and the exact
fiber-inclusion formula. -/

open Set _root_.Metric
open scoped _root_.Manifold ContDiff _root_.Topology

open OAI.ArithmeticGeometry.Descent.CMVariety.FamilyLogarithm.Abelian

variable {P V X : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P] [FiniteDimensional ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V] [TopologicalSpace X]
  (E G : P → Type)
  [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
  [∀ p, FiniteDimensional ℝ (E p)] [∀ p, CompleteSpace (E p)]
  [∀ p, TopologicalSpace (G p)] [∀ p, ChartedSpace (E p) (G p)]
  [∀ p, CommGroup (G p)] [∀ p, LieGroup (𝓘(ℝ, E p)) ∞ (G p)] [∀ p, T2Space (G p)]

theorem exists_holomorphic_total_chart_logarithm
    (c : ∀ p, OpenPartialHomeomorph (G p) V) (embed : ∀ p, G p → X)
    (e : OpenPartialHomeomorph X (P × V)) (B : Set P) (hB : IsOpen B) (p₀ : P) (hp₀ : p₀ ∈ B)
    (hc : ∀ p ∈ B, (c p).MDifferentiable (𝓘(ℝ, E p)) (𝓘(ℝ, V)))
    (h1 : ∀ p ∈ B, (1 : G p) ∈ (c p).source) (h0 : ∀ p ∈ B, c p 1 = 0)
    (hsource : ∀ p ∈ B, (c p).source = (embed p) ⁻¹' e.source)
    (hforward : ∀ p ∈ B, ∀ z ∈ (c p).source, c p z = (e (embed p z)).2)
    (hinverse : ∀ p ∈ B, ∀ v ∈ (c p).target, embed p ((c p).symm v) = e.symm (p, v))
    (U : Set (P × V)) (hU : IsOpen U) (hU₀ : (p₀, (0 : V)) ∈ U)
    (hcont : ContinuousOn (fun q : P × V => embed q.1 (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := E q.1) (c q.1) q.2)) U)
    (m : P × (V × V) → V) (D : Set (P × (V × V))) (hD : IsOpen D)
    (hD₀ : (p₀, ((0 : V), 0)) ∈ D) (hm : ContDiffOn ℂ 3 m D)
    (hcomparison : ∀ p ∈ B, ∀ u v, (p, (u, v)) ∈ D →
      m (p, (u, v)) = c p ((c p).symm u * (c p).symm v)) :
    ∃ (W : Set P) (δ r : ℝ) (logarithm : P × V → V),
      IsOpen W ∧ p₀ ∈ W ∧ W ⊆ B ∧ 0 < δ ∧ 0 < r ∧ r ≤ δ / 2 ∧
      ContinuousOn logarithm (W ×ˢ closedBall (0 : V) (δ / 2)) ∧
      DifferentiableOn ℂ logarithm (W ×ˢ ball (0 : V) r) ∧
      (∀ p ∈ W, ∀ y ∈ closedBall (0 : V) (δ / 2),
        logarithm (p, y) ∈ closedBall (0 : V) δ ∧
        ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := E p) (c p) (logarithm (p, y)) ∈ (c p).source ∧
        c p (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := E p) (c p) (logarithm (p, y))) = y ∧
        embed p (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := E p) (c p) (logarithm (p, y))) = e.symm (p, y)) ∧
      ∀ p ∈ W, ∀ v ∈ closedBall (0 : V) δ,
        c p (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := E p) (c p) v) ∈ closedBall (0 : V) (δ / 2) →
          logarithm (p, c p (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := E p) (c p) v)) = v := by
  let : CompleteSpace V := FiniteDimensional.complete ℂ V
  let φ := fun q : P × V => embed q.1 (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := E q.1) (c q.1) q.2)
  let U₁ := U ∩ {q : P × V | q.1 ∈ B}
  have hU₁ : IsOpen U₁ := hU.inter (hB.preimage continuous_fst)
  let Ω := U₁ ∩ φ ⁻¹' e.source
  have hΩ : IsOpen Ω := (hcont.mono inter_subset_left).isOpen_inter_preimage hU₁ e.open_source
  have hφ₀ : φ (p₀, 0) ∈ e.source := by
    change embed p₀ (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := E p₀) (c p₀) 0) ∈ e.source
    rw [ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential_zero]
    have hs := h1 p₀ hp₀
    rw [hsource p₀ hp₀] at hs
    exact hs
  have hΩ₀ : (p₀, (0 : V)) ∈ Ω := ⟨⟨hU₀, hp₀⟩, hφ₀⟩
  have hinside (q : P × V) (hq : q ∈ Ω) :
      ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := E q.1) (c q.1) q.2 ∈ (c q.1).source := by
    rw [hsource q.1 hq.1.2]
    exact hq.2
  have hcoord : ContinuousOn
      (fun q : P × V => c q.1 (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := E q.1) (c q.1) q.2)) Ω := by
    have ht : ContinuousOn (fun q : P × V => (e (φ q)).2) Ω :=
      (e.continuousOn.comp (hcont.mono (fun _ hq => hq.1.1)) (fun _ hq => hq.2)).snd
    apply ht.congr
    intro q hq
    exact hforward q.1 hq.1.2 _ (hinside q hq)
  obtain ⟨W, δ, r, logarithm, hW, hpW, hWB, hδ, hr, hrδ, hinto, hlog, hhol, hright, hleft⟩ :=
    exists_constructed_holomorphic_chart_logarithm E G c B hc h1 h0 Ω hΩ p₀ hΩ₀
      (fun _ hq => hq.1.2) hinside hcoord m D hD hD₀ hm hcomparison
  refine ⟨W, δ, r, logarithm, hW, hpW, hWB, hδ, hr, hrδ, hlog, hhol, ?_, hleft⟩
  intro p hp y hy
  have hin := hright p hp y hy
  have hs := hinside (p, logarithm (p, y)) (hinto ⟨hp, hin.1⟩)
  have ht : y ∈ (c p).target := hin.2 ▸ (c p).map_source hs
  have heq : ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := E p) (c p) (logarithm (p, y)) = (c p).symm y :=
    ((c p).left_inv hs).symm.trans (congrArg (c p).symm hin.2)
  exact ⟨hin.1, hs, hin.2, (congrArg (embed p) heq).trans (hinverse p (hWB hp) y ht)⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ConstructedHolomorphicLogarithm
