import OAI.Analysis.ODE.SmoothFlow.Flow
import OAI.Analysis.ODE.SmoothFlow.Cutoff

noncomputable section
open Set
open scoped Topology ContDiff

namespace OAI.Analysis.ODE.SmoothFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Smooth parameter dependence for the genuine local flow of a smooth vector
field on an open finite-dimensional domain. The initial point and time vary
jointly on one fixed open product neighborhood. -/
theorem exists_smooth_local_flow {U : Set E} (hU : IsOpen U)
    (f : E → E) (hf : ContDiffOn ℝ ∞ f U) {x₀ : E} (hx₀ : x₀∈U) :
    ∃ (ε : ℝ), 0<ε ∧ ∃ (V : Set E) (Φ : E×ℝ → E),
      IsOpen V ∧ x₀∈V ∧ V⊆U ∧
      ContDiffOn ℝ ∞ Φ (V×ˢIoo (-ε) ε) ∧
      (∀x∈V, Φ (x,0)=x) ∧ MapsTo Φ (V×ˢIoo (-ε) ε) U ∧
      ∀x∈V, ∀t∈Ioo (-ε) ε,
        HasDerivAt (fun s => Φ (x,s)) (f (Φ (x,t))) t := by
  obtain ⟨r,hr,hrU,f₀,hf₀,hsupp,heq⟩ := exists_global_smooth_agree hU hf hx₀
  obtain ⟨ε,hε,V,Φ,hV,hV₀,hVr,hΦ,hinitial,hmaps,hode⟩ :=
    exists_smooth_local_flow_global f₀ hf₀ x₀ hr
  refine ⟨ε,hε,V,Φ,hV,hV₀,fun x hx => hrU (Metric.ball_subset_closedBall (hVr hx)),
    hΦ,hinitial,fun p hp => hrU (Metric.ball_subset_closedBall (hmaps hp)),?_⟩
  intro x hx t ht
  have he : f₀ (Φ (x,t)) = f (Φ (x,t)) :=
    heq (Metric.ball_subset_closedBall (hmaps ⟨hx,ht⟩))
  rw [←he]
  exact hode x hx t ht

end OAI.Analysis.ODE.SmoothFlow
