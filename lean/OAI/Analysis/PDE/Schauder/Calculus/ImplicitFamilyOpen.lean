import OAI.Analysis.PDE.Schauder.Calculus.ImplicitFamily

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Schauder

variable {Z X Y : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- A continuous solution of an implicit equation agrees locally with
the smooth implicit branch at each point where the partial derivative is invertible. -/
theorem contDiffAt_of_continuous_implicit_solution
    {Q : Z × X → Y} {v : Z → X} {z : Z}
    (hQ : ContDiffAt ℝ ∞ Q (z,v z)) (hv : ContinuousAt v z)
    (hder : ((fderiv ℝ Q (z,v z)).comp (ContinuousLinearMap.inr ℝ Z X)).IsInvertible)
    (heq : ∀ᶠ t in 𝓝 z, Q (t,v t) = Q (z,v z)) :
    ContDiffAt ℝ ∞ v z := by
  have hp : Tendsto (fun t => (t,v t)) (𝓝 z) (𝓝 (z,v z)) :=
    continuousAt_id.tendsto.prodMk_nhds hv.tendsto
  have hi := hp.eventually (hQ.eventually_apply_eq_iff_implicitFunction (by simp) hder)
  apply (hQ.contDiffAt_implicitFunction (by simp) hder).congr_of_eventuallyEq
  filter_upwards [hi,heq] with t ht he
  exact ((ht).mp he).symm

/-- For a residual smooth on an open set, a single open parameter
neighborhood carries the smooth implicit solution of every order. -/
theorem exists_smooth_implicit_family_open
    (Q : Z × X → Y) (z₀ : Z) (v₀ : X) {S : Set (Z × X)}
    (hS : IsOpen S) (hQ : ContDiffOn ℝ ∞ Q S) (hbase : (z₀,v₀) ∈ S)
    (hzero : Q (z₀,v₀) = 0)
    (hder : ((fderiv ℝ Q (z₀,v₀)).comp (ContinuousLinearMap.inr ℝ Z X)).IsInvertible)
    {N : Set (Z × X)} (hN : N ∈ 𝓝 (z₀,v₀)) :
    ∃ (v : Z → X) (W : Set Z), IsOpen W ∧ z₀ ∈ W ∧
      ContDiffOn ℝ ∞ v W ∧ v z₀ = v₀ ∧
      ∀ z ∈ W, (z,v z) ∈ N ∧ Q (z,v z) = 0 := by
  have hQa := (hQ (z₀,v₀) hbase).contDiffAt (hS.mem_nhds hbase)
  obtain ⟨v,hv,hv0,he⟩ := exists_smooth_implicit_family Q z₀ v₀ hQa hzero hder hN
  have hp : Tendsto (fun z => (z,v z)) (𝓝 z₀) (𝓝 (z₀,v₀)) := by
    simpa only [hv0,id_eq] using continuousAt_id.tendsto.prodMk_nhds hv.continuousAt.tendsto
  have hd : ContinuousAt (fun p : Z × X =>
      (fderiv ℝ Q p).comp (ContinuousLinearMap.inr ℝ Z X)) (z₀,v₀) :=
    ((hQa.fderiv_right (m := 0) (by simp)).continuousAt).clm_comp continuousAt_const
  have hdi := hp.eventually (hd.tendsto.eventually hder.eventually_nhds)
  have hvc : ∀ᶠ z in 𝓝 z₀, ContinuousAt v z :=
    ((hv.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)).mono
      (fun z hz => hz.continuousAt)
  have hall := ((he.and (hp.eventually (hS.eventually_mem hbase))).and hdi).and hvc
  obtain ⟨W,hWsub,hW,hW0⟩ := mem_nhds_iff.mp hall
  refine ⟨v,W,hW,hW0,?_,hv0,fun z hz => (hWsub hz).1.1.1⟩
  intro z hz
  have hh := hWsub hz
  apply ContDiffAt.contDiffWithinAt
  apply contDiffAt_of_continuous_implicit_solution
    ((hQ (z,v z) hh.1.1.2).contDiffAt (hS.mem_nhds hh.1.1.2)) hh.2 hh.1.2
  filter_upwards [hW.eventually_mem hz] with t ht
  exact (hWsub ht).1.1.1.2.trans hh.1.1.1.2.symm

end OAI.Analysis.PDE.Schauder
