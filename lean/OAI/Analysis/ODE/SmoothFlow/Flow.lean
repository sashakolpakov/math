import OAI.Analysis.ODE.SmoothFlow.Implicit
import OAI.Analysis.ODE.SmoothFlow.Comparison

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

namespace OAI.Analysis.ODE.SmoothFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Local smooth dependence of genuine autonomous ODE solutions, with a
prescribed open ball controlling the values of the flow. -/
theorem exists_smooth_local_flow_global (f : E → E) (hf : ContDiff ℝ ∞ f)
    (x₀ : E) {R : ℝ} (hR : 0<R) :
    ∃ (ε : ℝ), 0<ε ∧ ∃ (V : Set E) (Φ : E×ℝ → E),
      IsOpen V ∧ x₀∈V ∧ V⊆ball x₀ R ∧
      ContDiffOn ℝ ∞ Φ (V×ˢIoo (-ε) ε) ∧
      (∀x∈V, Φ (x,0)=x) ∧
      MapsTo Φ (V×ˢIoo (-ε) ε) (ball x₀ R) ∧
      ∀x∈V, ∀t∈Ioo (-ε) ε,
        HasDerivAt (fun s => Φ (x,s)) (f (Φ (x,t))) t := by
  obtain ⟨γ,W,hW,hW₀,hγ,hγ₀,hsol⟩ := exists_smooth_path_family f hf x₀ hR
  obtain ⟨δ,hδ,hδW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hW₀)
  let ε := δ/2
  have hε : 0<ε := half_pos hδ
  have hεδ : ε<δ := half_lt_self hδ
  let V := ball x₀ ε
  let Φ : E×ℝ → E := fun p => γ p ⟨1,by norm_num⟩
  have hpW : ∀x∈V, ∀t:ℝ, |t|≤ε → (x,t)∈W := by
    intro x hx t ht
    apply hδW
    rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, sub_zero]
    exact ⟨lt_trans hx hεδ, lt_of_le_of_lt ht hεδ⟩
  have hinitial : ∀x∈V, Φ (x,0)=x := by
    intro x hx
    have he := (hsol (x,0) (hpW x hx 0 (by simpa using hε.le))).2
    simp only [zero_smul,add_zero] at he
    change γ (x,0) ⟨1,by norm_num⟩=x
    rw [he]
    rfl
  have hmaps : MapsTo Φ (V×ˢIoo (-ε) ε) (ball x₀ R) := by
    intro p hp
    have hb := (hsol p (hpW p.1 hp.1 p.2 (abs_lt.mpr hp.2).le)).1
    exact (ContinuousMap.dist_apply_le_dist (⟨1,by norm_num⟩:TimeInterval)).trans_lt hb
  obtain ⟨L,hL⟩ := hf.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall x₀ R) (isCompact_closedBall x₀ R)
  have hcomparison : ∀x∈V, ∀t∈Ioo (-ε) ε,
      Φ (x,t) = extendPath (γ (x,ε)) (t/ε) := by
    intro x hx t ht
    have hxε := hpW x hx ε (by rw [abs_of_pos hε])
    have hxt := hpW x hx t (abs_lt.mpr ht).le
    exact fixedPoint_endpoint_eq_rescaled f hf.continuous hL hε (abs_lt.mpr ht)
      (γ (x,t)) (γ (x,ε)) (hsol _ hxt).2 (hsol _ hxε).2
      (hsol _ hxt).1 (hsol _ hxε).1
  refine ⟨ε,hε,V,Φ,isOpen_ball,mem_ball_self hε,?_,?_,hinitial,hmaps,?_⟩
  · intro x hx
    have h := hmaps (show (x,(0:ℝ))∈V×ˢIoo (-ε) ε by exact ⟨hx,by constructor <;> linarith⟩)
    rwa [hinitial x hx] at h
  · exact (ContinuousMap.evalCLM ℝ (M:=E) (⟨1,by norm_num⟩:TimeInterval)).contDiff.comp_contDiffOn
      (hγ.mono (show V×ˢIoo (-ε) ε ⊆ W from
        fun p hp => hpW p.1 hp.1 p.2 (abs_lt.mpr hp.2).le))
  · intro x hx t ht
    have hratio : t/ε∈Ioo (-1:ℝ) 1 := by
      apply abs_lt.mp
      rw [abs_div,abs_of_pos hε,div_lt_one hε]
      exact abs_lt.mpr ht
    have hxε := hpW x hx ε (by rw [abs_of_pos hε])
    have hd := nonlinear_fixedPoint_rescaled_hasDerivAt ⟨f,hf.continuous⟩
      (hsol (x,ε) hxε).2 (ne_of_gt hε) hratio
    change HasDerivAt (fun s => extendPath (γ (x,ε)) (s/ε))
      (f (extendPath (γ (x,ε)) (t/ε))) t at hd
    rw [←hcomparison x hx t ht] at hd
    apply hd.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hcomparison x hx s hs

end OAI.Analysis.ODE.SmoothFlow
