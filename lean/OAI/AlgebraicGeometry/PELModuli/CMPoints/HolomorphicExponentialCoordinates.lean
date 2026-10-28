import OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicExponentialFromLogarithm
import OAI.ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative

/-! # Holomorphic Exponential Coordinates -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicExponentialCoordinates

noncomputable section

/-! The literal chart exponential depends holomorphically on base and
velocity near the identity. Its continuity is recovered from the actual
total-space exponential and the exact chart comparison. -/

open Set _root_.Metric Filter
open scoped _root_.Topology _root_.Manifold ContDiff

open OAI.ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian

variable {P V X : Type}
  [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V] [TopologicalSpace X]
  (L G : P → Type)
  [∀ p, NormedAddCommGroup (L p)] [∀ p, NormedSpace ℝ (L p)]
  [∀ p, FiniteDimensional ℝ (L p)] [∀ p, CompleteSpace (L p)]
  [∀ p, TopologicalSpace (G p)] [∀ p, ChartedSpace (L p) (G p)]
  [∀ p, CommGroup (G p)] [∀ p, LieGroup (𝓘(ℝ, L p)) ∞ (G p)] [∀ p, T2Space (G p)]

theorem exists_holomorphic_chart_exponential_coordinates
    (c : ∀ p, OpenPartialHomeomorph (G p) V) (embed : ∀ p, G p → X)
    (e : OpenPartialHomeomorph X (P × V)) (B : Set P) (hB : IsOpen B)
    (p₀ : P) (hp₀ : p₀ ∈ B)
    (hc : ∀ p ∈ B, (c p).MDifferentiable (𝓘(ℝ, L p)) (𝓘(ℝ, V)))
    (h1 : ∀ p ∈ B, (1 : G p) ∈ (c p).source) (h0 : ∀ p ∈ B, c p 1 = 0)
    (hsource : ∀ p ∈ B, (c p).source = (embed p) ⁻¹' e.source)
    (hforward : ∀ p ∈ B, ∀ z ∈ (c p).source, c p z = (e (embed p z)).2)
    (hcont : ContinuousAt (fun q : P × V =>
      embed q.1 (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q.1) (c q.1) q.2)) (p₀, 0))
    (δ r : ℝ) (hδ : 0 < δ) (hr : 0 < r) (hrδ : r ≤ δ / 2)
    (logarithm : P × V → V)
    (hlog : DifferentiableOn ℂ logarithm (B ×ˢ ball 0 r))
    (hright : ∀ p ∈ B, ∀ y ∈ closedBall (0 : V) (δ / 2),
      c p (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L p) (c p) (logarithm (p, y))) = y)
    (hleft : ∀ p ∈ B, ∀ v ∈ closedBall (0 : V) δ,
      c p (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L p) (c p) v) ∈ closedBall (0 : V) (δ / 2) →
        logarithm (p, c p (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L p) (c p) v)) = v) :
    ∃ U : Set (P × V), IsOpen U ∧ (p₀, (0 : V)) ∈ U ∧
      DifferentiableOn ℂ (fun q : P × V =>
        c q.1 (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q.1) (c q.1) q.2)) U := by
  let f := fun q : P × V => c q.1 (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q.1) (c q.1) q.2)
  let φ := fun q : P × V => embed q.1 (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q.1) (c q.1) q.2)
  have hunit : φ (p₀, 0) ∈ e.source := by
    dsimp only [φ]
    rw [ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential_zero]
    have h := h1 p₀ hp₀
    rw [hsource p₀ hp₀] at h
    exact h
  have heq : f =ᶠ[𝓝 (p₀, (0 : V))] (fun q => (e (φ q)).2) := by
    have hb := (continuousAt_fst (p := (p₀, (0 : V)))).preimage_mem_nhds (hB.mem_nhds hp₀)
    have hs := hcont.preimage_mem_nhds (e.open_source.mem_nhds hunit)
    filter_upwards [hb, hs] with q hq hsq
    apply hforward q.1 hq
    rw [hsource q.1 hq]
    exact hsq
  have hf : ContinuousAt f (p₀, 0) :=
    ((e.continuousAt hunit).comp hcont).snd.congr_of_eventuallyEq heq
  apply HolomorphicExponentialFromLogarithm.exists_holomorphic_exponential_of_logarithm f logarithm B hB p₀ hp₀ δ r hδ hr hf
  · intro p hp
    dsimp only [f]
    rw [ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential_zero, h0 p hp]
  · exact ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponentialCoordinates_hasFDerivAt_zero (c p₀) (hc p₀ hp₀) (h1 p₀ hp₀) (h0 p₀ hp₀)
  · exact hlog
  · intro y hy
    exact hright p₀ hp₀ y (mem_closedBall.mpr ((mem_ball.mp hy).le.trans hrδ))
  · exact hleft

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicExponentialCoordinates
