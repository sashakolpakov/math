import OAI.ArithmeticGeometry.Descent.CMVariety.ExponentialChartODE
import OAI.ArithmeticGeometry.Descent.CMVariety.MultiplicationFieldFlow
import OAI.ArithmeticGeometry.Descent.CMVariety.FlowNeighborhoods

/-! # Local Exponential Family -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.LocalExponentialFamily.Abelian

noncomputable section

/-!
Construct continuous relative exponentials from local multiplication
coordinates. The common flow, its containment in the chart, and its
identification with the actual invariant exponential are all proved.
-/

open Set _root_.Metric
open scoped _root_.Manifold ContDiff _root_.Topology NNReal

variable {P V X : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [TopologicalSpace X]
  (E G : P → Type)
  [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)] [∀ p, CompleteSpace (E p)]
  [∀ p, TopologicalSpace (G p)] [∀ p, ChartedSpace (E p) (G p)]
  [∀ p, Group (G p)] [∀ p, LieGroup (𝓘(ℝ, E p)) ∞ (G p)] [∀ p, T2Space (G p)]

/-- A jointly smooth local multiplication constructs a jointly continuous
actual exponential near the identity section, even when the native fiber
models vary with the parameter. -/
theorem exists_continuous_local_exponential_family
    (c : ∀ p, OpenPartialHomeomorph (G p) V)
    (embed : ∀ p, G p → X) (coordinates : P × V → X)
    (U : Set P) (hU : IsOpen U) (p₀ : P) (hp₀ : p₀ ∈ U)
    (Ω : Set (P × V)) (hΩ : IsOpen Ω) (hΩ₀ : (p₀, 0) ∈ Ω)
    (hc : ∀ p ∈ U, (c p).MDifferentiable (𝓘(ℝ, E p)) (𝓘(ℝ, V)))
    (h1 : ∀ p ∈ U, (1 : G p) ∈ (c p).source)
    (h0 : ∀ p ∈ U, c p 1 = 0)
    (htarget : ∀ p ∈ U, (c p).target = {v | (p, v) ∈ Ω})
    (hcoordinates : ContinuousOn coordinates Ω)
    (hinverse : ∀ p ∈ U, ∀ v ∈ (c p).target, embed p ((c p).symm v) = coordinates (p, v))
    (m : P × (V × V) → V) (hm : ContDiffAt ℝ 2 m (p₀, (0, 0)))
    (D : Set (P × (V × V))) (hD : IsOpen D) (hD₀ : (p₀, (0, 0)) ∈ D)
    (hcomparison : ∀ p ∈ U, ∀ u v, (p, (u, v)) ∈ D →
      m (p, (u, v)) = c p ((c p).symm u * (c p).symm v)) :
    ∃ r : ℝ≥0, 0 < r ∧ ∃ ε : ℝ, 0 < ε ∧
      (∀ q ∈ closedBall (p₀, (0 : V)) r, q.1 ∈ U) ∧
      ContinuousOn
        (fun z : (P × V) × ℝ => embed z.1.1
          (AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.exp (E := E z.1.1) (z.2 • ExponentialChartODE.Abelian.chartVelocity (E := E z.1.1) (c z.1.1) z.1.2)))
        (closedBall (p₀, (0 : V)) r ×ˢ Ioo (-ε) ε) := by
  obtain ⟨r, hr, ε, hε, flow, hflow, hf⟩ :=
    MultiplicationFieldFlow.Abelian.exists_continuous_multiplicationField_flow m p₀ hm
  let W : Set ((P × V) × V) :=
    {z | z.1.1 ∈ U ∧ (z.1.1, z.2) ∈ Ω ∧ (z.1.1, (z.2, 0)) ∈ D}
  have hW : IsOpen W :=
    (hU.preimage continuous_fst.fst).inter
      ((hΩ.preimage (continuous_fst.fst.prodMk continuous_snd)).inter
        (hD.preimage (continuous_fst.fst.prodMk (continuous_snd.prodMk continuous_const))))
  have hW₀ : ((p₀, (0 : V)), (0 : V)) ∈ W := ⟨hp₀, hΩ₀, hD₀⟩
  obtain ⟨r', hr', hrr, ε', hε', hεε, hinto⟩ := FlowNeighborhoods.Abelian.exists_uniform_flow_neighborhood
    flow (p₀, 0) r hr ε hε hflow (hf _ (mem_closedBall_self (le_of_lt hr))).1 W hW hW₀
  have hball : closedBall (p₀, (0 : V)) (r' : ℝ) ⊆ closedBall (p₀, (0 : V)) (r : ℝ) :=
    closedBall_subset_closedBall hrr
  have htime : Ioo (-ε') ε' ⊆ Ioo (-ε) ε := Ioo_subset_Ioo (neg_le_neg hεε) hεε
  have ht0 : (0 : ℝ) ∈ Ioo (-ε') ε' := ⟨by linarith, hε'⟩
  have hbase (q : P × V) (hq : q ∈ closedBall (p₀, (0 : V)) r') : q.1 ∈ U :=
    (hinto q hq 0 ht0).1
  have htarget' (q : P × V) (hq : q ∈ closedBall (p₀, (0 : V)) r')
      (t : ℝ) (ht : t ∈ Ioo (-ε') ε') : flow (q, t) ∈ (c q.1).target := by
    rw [htarget q.1 (hbase q hq)]
    exact (hinto q hq t ht).2.1
  have hderiv (q : P × V) (hq : q ∈ closedBall (p₀, (0 : V)) r')
      (t : ℝ) (ht : t ∈ Ioo (-ε') ε') :
      HasDerivAt (fun τ => flow (q, τ))
        (fderiv ℝ (fun y => c q.1 ((c q.1).symm (flow (q, t)) * (c q.1).symm y)) 0 q.2) t := by
    have hd : (q.1, (flow (q, t), (0 : V))) ∈ D := (hinto q hq t ht).2.2
    have heq : (fun y => m (q.1, (flow (q, t), y))) =ᶠ[𝓝 (0 : V)]
        (fun y => c q.1 ((c q.1).symm (flow (q, t)) * (c q.1).symm y)) := by
      have hmem := (continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousAt
        |>.preimage_mem_nhds (hD.mem_nhds hd)
      filter_upwards [hmem] with y hy
      exact hcomparison q.1 (hbase q hq) (flow (q, t)) y hy
    rw [← heq.fderiv_eq]
    exact (hf q (hball hq)).2 t (htime ht)
  have hcont : ContinuousOn (fun z : (P × V) × ℝ => coordinates (z.1.1, flow z))
      (closedBall (p₀, (0 : V)) r' ×ˢ Ioo (-ε') ε') :=
    hcoordinates.comp
      (continuousOn_fst.fst.prodMk (hflow.mono (prod_mono hball htime)))
      (fun z hz => (hinto z.1 hz.1 z.2 hz.2).2.1)
  refine ⟨r', hr', ε', hε', hbase, hcont.congr ?_⟩
  rintro ⟨q, t⟩ ⟨hq, ht⟩
  have heq := ExponentialChartODE.Abelian.chartODE_eq_exponential (E := E q.1) (c q.1)
    (hc q.1 (hbase q hq)) (h1 q.1 (hbase q hq)) (h0 q.1 (hbase q hq))
    q.2 (fun τ => flow (q, τ)) ε' hε' (hf q (hball hq)).1
    (htarget' q hq) (hderiv q hq) t ht
  exact (congrArg (embed q.1) heq).symm.trans
    (hinverse q.1 (hbase q hq) (flow (q, t)) (htarget' q hq t ht))

end

end OAI.ArithmeticGeometry.Descent.CMVariety.LocalExponentialFamily.Abelian
