import OAI.Analysis.PDE.Schauder.Calculus.Periodic.HolderBound
import Mathlib.Topology.ContinuousMap.Compact

open Set Filter Metric Module
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder

variable {E P V F I A : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype I]
  [TopologicalSpace A]

def compactParameterCurry {S : Set E} (f : A → E → F)
    (hf : Continuous (fun z : A × E => f z.1 z.2)) (a : A) : C(S,F) :=
  ⟨fun x => f a x, hf.comp (continuous_const.prodMk continuous_subtype_val)⟩

omit [NormedSpace ℝ E] [ProperSpace E] [NormedSpace ℝ F] in
theorem continuous_compactParameterCurry {S : Set E} [CompactSpace S]
    (f : A → E → F) (hf : Continuous (fun z : A × E => f z.1 z.2)) :
    Continuous (compactParameterCurry (S := S) f hf) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact hf.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

/-- Joint continuity of a periodic field and its spatial derivative gives
continuity in the global Hölder norm, on every exponent at most one. -/
theorem continuous_periodic_holder_family
    (e : E ≃L[ℝ] P × V) (b : Basis I ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (f : A → E → F) (T : A → OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} F α)
    (hf : Continuous (fun z : A × E => f z.1 z.2))
    (hD : Continuous (fun z : A × E => fderiv ℝ (f z.1) z.2))
    (hd : ∀ a x, DifferentiableAt ℝ (f a) x)
    (hp : ∀ a, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (f a))
    (hT : ∀ a x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (T a) x = f a x) : Continuous T := by
  obtain ⟨R,hR,hcontrol⟩ := exists_periodic_holder_control_ball
    (F := F) e b hK hr hrp hbounded hα hα1
  let S := closedBall (0 : E) R
  have : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E) R)
  let c := compactParameterCurry (S := S) f hf
  let d := compactParameterCurry (S := S) (fun a x => fderiv ℝ (f a) x) hD
  have hc : Continuous c := continuous_compactParameterCurry f hf
  have hdc : Continuous d := continuous_compactParameterCurry _ hD
  apply continuous_iff_continuousAt.mpr
  intro a
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hce : ∀ᶠ t in 𝓝 a, dist (c t) (c a) < ε/8 :=
    (Metric.tendsto_nhds.mp (hc.continuousAt (x := a))) (ε/8) (by positivity)
  have hde : ∀ᶠ t in 𝓝 a, dist (d t) (d a) < ε/8 :=
    (Metric.tendsto_nhds.mp (hdc.continuousAt (x := a))) (ε/8) (by positivity)
  filter_upwards [hce,hde] with t ht hdt
  have hB x (hx : x ∈ S) : ‖f t x-f a x‖ ≤ ε/8 := by
    have h := ContinuousMap.norm_coe_le_norm (c t-c a) ⟨x,hx⟩
    exact h.trans (le_of_lt (by simpa only [dist_eq_norm] using ht))
  have hDB x (hx : x ∈ S) : ‖fderiv ℝ (f t) x-fderiv ℝ (f a) x‖ ≤ ε/8 := by
    have h := ContinuousMap.norm_coe_le_norm (d t-d a) ⟨x,hx⟩
    exact h.trans (le_of_lt (by simpa only [dist_eq_norm] using hdt))
  have hnorm := hcontrol (fun x => f t x-f a x) (T t-T a) (ε/8) (by positivity)
    (fun x l => by dsimp only; rw [hp t x l,hp a x l])
    (fun x _ => (hd t x).sub (hd a x)) hB
    (fun x hx => by
      have he : fderiv ℝ (fun x => f t x-f a x) x =
          fderiv ℝ (f t) x-fderiv ℝ (f a) x := by
        simpa only [Pi.sub_apply] using! fderiv_sub (hd t x) (hd a x)
      rw [he]
      exact hDB x hx)
    (fun x => by change OAI.Analysis.Normed.Function.Holder.HolderMap.value (T t) x-OAI.Analysis.Normed.Function.Holder.HolderMap.value (T a) x = _; rw [hT,hT])
  rw [dist_eq_norm]
  exact hnorm.trans_lt (by linarith)

end OAI.Analysis.PDE.Schauder
