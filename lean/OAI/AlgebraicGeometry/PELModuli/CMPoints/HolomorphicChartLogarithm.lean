import OAI.AlgebraicGeometry.PELModuli.CMPoints.ChartLogarithmDifferential
import OAI.AlgebraicGeometry.PELModuli.CMPoints.InvariantDifferential
import OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicInverseFamily

/-! # Holomorphic Chart Logarithm -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicChartLogarithm

noncomputable section

/-! The common continuous logarithm of the actual chart exponential is
holomorphic in the base and target. Its inverse differential is derived
from the given analytic multiplication law. -/

open Set _root_.Metric
open scoped _root_.Topology _root_.Manifold ContDiff Classical

variable {P V : Type} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [FiniteDimensional ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V]
  (L G : P → Type)
  [∀ p, NormedAddCommGroup (L p)] [∀ p, NormedSpace ℝ (L p)]
  [∀ p, FiniteDimensional ℝ (L p)] [∀ p, CompleteSpace (L p)]
  [∀ p, TopologicalSpace (G p)] [∀ p, ChartedSpace (L p) (G p)]
  [∀ p, CommGroup (G p)] [∀ p, LieGroup (𝓘(ℝ, L p)) ∞ (G p)] [∀ p, T2Space (G p)]

theorem exists_holomorphic_chart_logarithm_neighborhood
    (c : ∀ p, OpenPartialHomeomorph (G p) V) (B : Set P) (hB : IsOpen B)
    (hc : ∀ p ∈ B, (c p).MDifferentiable (𝓘(ℝ, L p)) (𝓘(ℝ, V)))
    (h1 : ∀ p ∈ B, (1 : G p) ∈ (c p).source) (h0 : ∀ p ∈ B, c p 1 = 0)
    (m : P × (V × V) → V) (D : Set (P × (V × V))) (hD : IsOpen D)
    (hm : ContDiffOn ℂ 3 m D)
    (hcomparison : ∀ p ∈ B, ∀ u w, (p, (u, w)) ∈ D →
      m (p, (u, w)) = c p ((c p).symm u * (c p).symm w))
    (p₀ : P) (hp₀ : p₀ ∈ B) (hD₀ : (p₀, ((0 : V), 0)) ∈ D)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (logarithm : P × V → V)
    (hlog : ContinuousOn logarithm (B ×ˢ ball 0 r₀))
    (hright : ∀ p ∈ B, ∀ y ∈ ball 0 r₀,
      ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L p) (c p) (logarithm (p, y)) ∈ (c p).source ∧
      c p (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L p) (c p) (logarithm (p, y))) = y)
    (hzero : ∀ p ∈ B, logarithm (p, 0) = 0) :
    ∃ (U : Set P) (r : ℝ), IsOpen U ∧ p₀ ∈ U ∧ U ⊆ B ∧ 0 < r ∧ r ≤ r₀ ∧
      DifferentiableOn ℂ logarithm (U ×ˢ ball 0 r) := by
  let : CompleteSpace V := FiniteDimensional.complete ℂ V
  let Ω : Set (P × V) := {q | (q.1, (q.2, (0 : V))) ∈ D}
  have hΩ : IsOpen Ω := hD.preimage
    (continuous_fst.prodMk (continuous_snd.prodMk continuous_const))
  let A : P × V → V →L[ℂ] V := fun q => fderiv ℂ (fun w => m (q.1, (q.2, w))) 0
  have hA : ContDiffOn ℂ 2 A Ω := InvariantDifferential.contDiffOn_multiplication_differential m D hD hm
  have hA₀ : A (p₀, 0) = (ContinuousLinearEquiv.refl ℂ V).toContinuousLinearMap :=
    ChartLogarithmDifferential.multiplication_differential_at_identity (c p₀) (h1 p₀ hp₀) (h0 p₀ hp₀)
      m D hD p₀ (hcomparison p₀ hp₀) hD₀
  obtain ⟨W, e, hW, hpW, hWΩ, he, heInv⟩ :=
    InvariantDifferential.exists_holomorphic_inverse_differential_neighborhood A Ω hΩ hA (p₀, 0) hD₀
      (ContinuousLinearEquiv.refl ℂ V) hA₀
  have hN : IsOpen (W ∩ (B ×ˢ ball (0 : V) r₀)) := hW.inter (hB.prod isOpen_ball)
  have hpN : (p₀, (0 : V)) ∈ W ∩ (B ×ˢ ball (0 : V) r₀) :=
    ⟨hpW, hp₀, mem_ball_self hr₀⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hN (p₀, 0) hpN
  let U : Set P := ball p₀ ε
  let r := min ε r₀
  have hr : 0 < r := lt_min hε hr₀
  have hrectangle : U ×ˢ ball (0 : V) r ⊆ W ∩ (B ×ˢ ball (0 : V) r₀) := by
    intro q hq
    apply hεsub
    change dist (q.1, q.2) (p₀, (0 : V)) < ε
    rw [Prod.dist_eq]
    exact max_lt hq.1 ((mem_ball.mp hq.2).trans_le (min_le_left ε r₀))
  have hUB : U ⊆ B := by
    intro p hp
    have hq : (p, (0 : V)) ∈ U ×ˢ ball (0 : V) r := ⟨hp, mem_ball_self hr⟩
    exact (hrectangle hq).2.1
  have hrle : r ≤ r₀ := min_le_right ε r₀
  have hsmall : U ×ˢ ball (0 : V) r ⊆ B ×ˢ ball (0 : V) r₀ :=
    fun _ hq => (hrectangle hq).2
  refine ⟨U, r, isOpen_ball, mem_ball_self hε, hUB, hr, hrle, ?_⟩
  apply HolomorphicInverseFamily.differentiableOn_inverse_family_of_vertical_differential
    (fun q => c q.1 (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L q.1) (c q.1) q.2)) logarithm e U isOpen_ball r
    (hlog.mono hsmall)
  · intro p hp y hy
    have hq := hrectangle (show (p, y) ∈ U ×ˢ ball (0 : V) r from ⟨hp, hy⟩)
    have ht := hright p hq.2.1 y hq.2.2
    have h := ChartLogarithmDifferential.chart_exponential_complex_multiplication_differential (c p)
      (hc p hq.2.1) (h1 p hq.2.1) (h0 p hq.2.1) m D hD
      (hm.of_le (by norm_num : (1 : ℕ∞ω) ≤ 3)) p (hcomparison p hq.2.1)
      (logarithm (p, y)) y ht.1 ht.2 (hWΩ hq.1)
    change HasFDerivAt (fun v => c p (ArithmeticGeometry.Descent.CMVariety.ChartEndomorphismDerivative.Abelian.chartExponential (E := L p) (c p) v))
      ((e (p, y)).toContinuousLinearMap.restrictScalars ℝ) (logarithm (p, y))
    rw [he (p, y) hq.1]
    exact h
  · intro p hp y hy
    have hq := hsmall (show (p, y) ∈ U ×ˢ ball (0 : V) r from ⟨hp, hy⟩)
    exact (hright p hq.1 y hq.2).2
  · exact fun p hp => hzero p (hUB hp)
  · exact heInv.mono (fun _ hq => (hrectangle hq).1)

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.HolomorphicChartLogarithm
