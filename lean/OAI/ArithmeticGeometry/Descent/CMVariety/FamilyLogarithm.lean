import OAI.ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative
import OAI.ArithmeticGeometry.Descent.CMVariety.MultiplicationDerivative
import OAI.ArithmeticGeometry.Descent.CMVariety.ParametricInverse

/-! # Family Logarithm -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.FamilyLogarithm.Abelian

noncomputable section

section

/-!
Construct a continuous local logarithm from actual exponential coordinates
and smooth multiplication coordinates. The vertical derivative, its joint
continuity, and its identity value at zero are derived before applying the
uniform inverse construction.
-/

open Set _root_.Metric
open scoped _root_.Manifold ContDiff _root_.Topology

variable {P V : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  (E G : P → Type)
  [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
  [∀ p, FiniteDimensional ℝ (E p)] [∀ p, CompleteSpace (E p)]
  [∀ p, TopologicalSpace (G p)] [∀ p, ChartedSpace (E p) (G p)]
  [∀ p, CommGroup (G p)] [∀ p, LieGroup (𝓘(ℝ, E p)) ∞ (G p)] [∀ p, T2Space (G p)]

/-- A jointly continuous chart exponential with the actual smooth local
multiplication has a jointly continuous logarithm on a common neighborhood.
No separately continuous vertical derivative or inverse is required. -/
theorem exists_continuous_chart_logarithm
    (c : ∀ p, OpenPartialHomeomorph (G p) V)
    (B : Set P)
    (hc : ∀ p ∈ B, (c p).MDifferentiable (𝓘(ℝ, E p)) (𝓘(ℝ, V)))
    (h1 : ∀ p ∈ B, (1 : G p) ∈ (c p).source) (h0 : ∀ p ∈ B, c p 1 = 0)
    (Ω : Set (P × V)) (hΩ : IsOpen Ω) (p₀ : P) (hp₀ : (p₀, (0 : V)) ∈ Ω)
    (hbase : ∀ q ∈ Ω, q.1 ∈ B)
    (hinside : ∀ q ∈ Ω, ChartEndomorphismDerivative.Abelian.chartExponential (E := E q.1) (c q.1) q.2 ∈ (c q.1).source)
    (hcont : ContinuousOn (fun q : P × V => c q.1 (ChartEndomorphismDerivative.Abelian.chartExponential (E := E q.1) (c q.1) q.2)) Ω)
    (m : P × (V × V) → V) (D : Set (P × (V × V))) (hD : IsOpen D)
    (hD₀ : (p₀, ((0 : V), 0)) ∈ D) (hm : ContDiffOn ℝ 2 m D)
    (hcomparison : ∀ p ∈ B, ∀ u v, (p, (u, v)) ∈ D →
      m (p, (u, v)) = c p ((c p).symm u * (c p).symm v)) :
    let f := fun q : P × V => c q.1 (ChartEndomorphismDerivative.Abelian.chartExponential (E := E q.1) (c q.1) q.2)
    ∃ (U : Set P) (δ : ℝ) (logarithm : P × V → V),
      IsOpen U ∧ p₀ ∈ U ∧ 0 < δ ∧ U ×ˢ closedBall (0 : V) δ ⊆ Ω ∧
      ContinuousOn logarithm (U ×ˢ closedBall (0 : V) (δ / 2)) ∧
      (∀ p ∈ U, ∀ y ∈ closedBall (0 : V) (δ / 2),
        logarithm (p, y) ∈ closedBall (0 : V) δ ∧ f (p, logarithm (p, y)) = y) ∧
      ∀ p ∈ U, ∀ v ∈ closedBall (0 : V) δ,
        f (p, v) ∈ closedBall (0 : V) (δ / 2) → logarithm (p, f (p, v)) = v := by
  dsimp only
  let f := fun q : P × V => c q.1 (ChartEndomorphismDerivative.Abelian.chartExponential (E := E q.1) (c q.1) q.2)
  let Ω' := Ω ∩ {q | (q.1, (f q, (0 : V))) ∈ D}
  have hΩ' : IsOpen Ω' :=
    (continuousOn_fst.prodMk (hcont.prodMk continuousOn_const)).isOpen_inter_preimage hΩ hD
  have hf₀ : f (p₀, 0) = 0 := by
    change c p₀ (ChartEndomorphismDerivative.Abelian.chartExponential (E := E p₀) (c p₀) 0) = 0
    rw [ChartEndomorphismDerivative.Abelian.chartExponential_zero, h0 p₀ (hbase _ hp₀)]
  have hp' : (p₀, (0 : V)) ∈ Ω' := by
    refine ⟨hp₀, ?_⟩
    change (p₀, (f (p₀, 0), (0 : V))) ∈ D
    rw [hf₀]
    exact hD₀
  let derivative : P × V → V →L[ℝ] V :=
    fun q => fderiv ℝ (fun y => m (q.1, (f q, y))) 0
  have hdercont : ContinuousOn derivative Ω' :=
    (MultiplicationDerivative.Abelian.continuousOn_multiplication_derivative m D hD hm).comp
      (continuousOn_fst.prodMk (hcont.mono inter_subset_left)) (fun _ hq => hq.2)
  have hderiv (q : P × V) (hq : q ∈ Ω') :
      HasFDerivAt (fun v => f (q.1, v)) (derivative q) q.2 := by
    have hnative := ChartEndomorphismDerivative.Abelian.chartExponentialCoordinates_hasFDerivAt (E := E q.1) (c q.1)
      (hc q.1 (hbase q hq.1)) (h1 q.1 (hbase q hq.1)) (h0 q.1 (hbase q hq.1))
      q.2 (hinside q hq.1)
    have heq : (fun y => m (q.1, (f q, y))) =ᶠ[𝓝 (0 : V)]
        (fun y => c q.1 ((c q.1).symm (f q) * (c q.1).symm y)) := by
      have hmem := (continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousAt
        |>.preimage_mem_nhds (hD.mem_nhds hq.2)
      filter_upwards [hmem] with y hy
      exact hcomparison q.1 (hbase q hq.1) (f q) y hy
    apply hnative.congr_fderiv
    exact heq.fderiv_eq.symm
  have hzero (p : P) (hp : (p, (0 : V)) ∈ Ω') : f (p, 0) = 0 := by
    change c p (ChartEndomorphismDerivative.Abelian.chartExponential (E := E p) (c p) 0) = 0
    rw [ChartEndomorphismDerivative.Abelian.chartExponential_zero, h0 p (hbase _ hp.1)]
  have hid : derivative (p₀, 0) = ContinuousLinearMap.id ℝ V :=
    (hderiv (p₀, 0) hp').unique
      (ChartEndomorphismDerivative.Abelian.chartExponentialCoordinates_hasFDerivAt_zero (E := E p₀) (c p₀)
        (hc p₀ (hbase _ hp₀)) (h1 p₀ (hbase _ hp₀)) (h0 p₀ (hbase _ hp₀)))
  obtain ⟨U, δ, logarithm, hU, hpU, hδ, hinto, hi, hr, hl⟩ :=
    ParametricInverse.Abelian.exists_local_continuous_parametric_inverse f derivative Ω' hΩ' p₀ hp'
      (hcont.mono inter_subset_left) hdercont hderiv hzero hid
  exact ⟨U, δ, logarithm, hU, hpU, hδ, hinto.trans inter_subset_left, hi, hr, hl⟩

end

/-!
Apply the logarithm construction to fiber charts cut out of a single
total-space chart. This separates the native scheme application from
the analytic inverse proof without adding an inverse as a hypothesis.
-/

open Set _root_.Metric
open scoped _root_.Manifold ContDiff _root_.Topology

variable {P V X : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] [TopologicalSpace X]
  (E G : P → Type)
  [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
  [∀ p, FiniteDimensional ℝ (E p)] [∀ p, CompleteSpace (E p)]
  [∀ p, TopologicalSpace (G p)] [∀ p, ChartedSpace (E p) (G p)]
  [∀ p, CommGroup (G p)] [∀ p, LieGroup (𝓘(ℝ, E p)) ∞ (G p)] [∀ p, T2Space (G p)]

theorem exists_total_chart_logarithm
    (c : ∀ p, OpenPartialHomeomorph (G p) V) (embed : ∀ p, G p → X)
    (e : OpenPartialHomeomorph X (P × V)) (B : Set P) (hB : IsOpen B) (p₀ : P) (hp₀ : p₀ ∈ B)
    (hc : ∀ p ∈ B, (c p).MDifferentiable (𝓘(ℝ, E p)) (𝓘(ℝ, V)))
    (h1 : ∀ p ∈ B, (1 : G p) ∈ (c p).source) (h0 : ∀ p ∈ B, c p 1 = 0)
    (hsource : ∀ p ∈ B, (c p).source = (embed p) ⁻¹' e.source)
    (hforward : ∀ p ∈ B, ∀ z ∈ (c p).source, c p z = (e (embed p z)).2)
    (hinverse : ∀ p ∈ B, ∀ v ∈ (c p).target, embed p ((c p).symm v) = e.symm (p, v))
    (U : Set (P × V)) (hU : IsOpen U) (hU₀ : (p₀, (0 : V)) ∈ U)
    (hcont : ContinuousOn (fun q : P × V => embed q.1 (ChartEndomorphismDerivative.Abelian.chartExponential (E := E q.1) (c q.1) q.2)) U)
    (m : P × (V × V) → V) (D : Set (P × (V × V))) (hD : IsOpen D)
    (hD₀ : (p₀, ((0 : V), 0)) ∈ D) (hm : ContDiffOn ℝ 2 m D)
    (hcomparison : ∀ p ∈ B, ∀ u v, (p, (u, v)) ∈ D →
      m (p, (u, v)) = c p ((c p).symm u * (c p).symm v)) :
    ∃ (W : Set P) (δ : ℝ) (logarithm : P × V → V),
      IsOpen W ∧ p₀ ∈ W ∧ W ⊆ B ∧ 0 < δ ∧
      ContinuousOn logarithm (W ×ˢ closedBall (0 : V) (δ / 2)) ∧
      (∀ p ∈ W, ∀ y ∈ closedBall (0 : V) (δ / 2),
        logarithm (p, y) ∈ closedBall (0 : V) δ ∧
        ChartEndomorphismDerivative.Abelian.chartExponential (E := E p) (c p) (logarithm (p, y)) ∈ (c p).source ∧
        embed p (ChartEndomorphismDerivative.Abelian.chartExponential (E := E p) (c p) (logarithm (p, y))) = e.symm (p, y)) ∧
      ∀ p ∈ W, ∀ v ∈ closedBall (0 : V) δ,
        c p (ChartEndomorphismDerivative.Abelian.chartExponential (E := E p) (c p) v) ∈ closedBall (0 : V) (δ / 2) →
          logarithm (p, c p (ChartEndomorphismDerivative.Abelian.chartExponential (E := E p) (c p) v)) = v := by
  let φ := fun q : P × V => embed q.1 (ChartEndomorphismDerivative.Abelian.chartExponential (E := E q.1) (c q.1) q.2)
  let U₁ := U ∩ {q : P × V | q.1 ∈ B}
  have hU₁ : IsOpen U₁ := hU.inter (hB.preimage continuous_fst)
  let Ω := U₁ ∩ φ ⁻¹' e.source
  have hΩ : IsOpen Ω := (hcont.mono inter_subset_left).isOpen_inter_preimage hU₁ e.open_source
  have hφ₀ : φ (p₀, 0) ∈ e.source := by
    change embed p₀ (ChartEndomorphismDerivative.Abelian.chartExponential (E := E p₀) (c p₀) 0) ∈ e.source
    rw [ChartEndomorphismDerivative.Abelian.chartExponential_zero]
    have hs := h1 p₀ hp₀
    rw [hsource p₀ hp₀] at hs
    exact hs
  have hΩ₀ : (p₀, (0 : V)) ∈ Ω := ⟨⟨hU₀, hp₀⟩, hφ₀⟩
  have hinside (q : P × V) (hq : q ∈ Ω) :
      ChartEndomorphismDerivative.Abelian.chartExponential (E := E q.1) (c q.1) q.2 ∈ (c q.1).source := by
    rw [hsource q.1 hq.1.2]
    exact hq.2
  have hcoord : ContinuousOn
      (fun q : P × V => c q.1 (ChartEndomorphismDerivative.Abelian.chartExponential (E := E q.1) (c q.1) q.2)) Ω := by
    have ht : ContinuousOn (fun q : P × V => (e (φ q)).2) Ω :=
      (e.continuousOn.comp (hcont.mono (fun _ hq => hq.1.1)) (fun _ hq => hq.2)).snd
    apply ht.congr
    intro q hq
    exact hforward q.1 hq.1.2 _ (hinside q hq)
  obtain ⟨W, δ, logarithm, hW, hpW, hδ, hinto, hlog, hright, hleft⟩ :=
    exists_continuous_chart_logarithm E G c B hc h1 h0 Ω hΩ p₀ hΩ₀
      (fun _ hq => hq.1.2) hinside hcoord m D hD hD₀ hm hcomparison
  have hWB : W ⊆ B := by
    intro p hp
    have h := hinto (a := (p, (0 : V))) ⟨hp, mem_closedBall_self (le_of_lt hδ)⟩
    exact h.1.2
  refine ⟨W, δ, logarithm, hW, hpW, hWB, hδ, hlog, ?_, hleft⟩
  intro p hp y hy
  have hin := hright p hp y hy
  have hs := hinside (p, logarithm (p, y)) (hinto ⟨hp, hin.1⟩)
  have ht : y ∈ (c p).target := hin.2 ▸ (c p).map_source hs
  have heq : ChartEndomorphismDerivative.Abelian.chartExponential (E := E p) (c p) (logarithm (p, y)) = (c p).symm y :=
    ((c p).left_inv hs).symm.trans (congrArg (c p).symm hin.2)
  exact ⟨hin.1, hs, (congrArg (embed p) heq).trans (hinverse p (hWB hp) y ht)⟩

end

end OAI.ArithmeticGeometry.Descent.CMVariety.FamilyLogarithm.Abelian
