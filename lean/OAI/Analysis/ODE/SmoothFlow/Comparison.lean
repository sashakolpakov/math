import OAI.Analysis.ODE.SmoothFlow.Superposition
import OAI.Analysis.ODE.SmoothFlow.FixedPoint
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section
open Set Metric
open scoped Topology ContDiff

namespace OAI.Analysis.ODE.SmoothFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem extendPath_mem_ball {γ : C(TimeInterval,E)} {x₀ : E} {R : ℝ}
    (hγ : dist γ (ContinuousMap.const TimeInterval x₀) < R) (s : ℝ) :
    extendPath γ s ∈ ball x₀ R := by
  exact (ContinuousMap.dist_apply_le_dist (timeClamp s)).trans_lt hγ

/-- Rescaling two actual integral-equation solutions identifies their endpoints.
The proof is uniqueness for the differential equation on the whole compact
unit interval, not a formal manipulation of a chosen flow. -/
theorem fixedPoint_endpoint_eq_rescaled
    (f : E → E) (hf : Continuous f) {x x₀ : E} {R τ t : ℝ} {L : NNReal}
    (hL : LipschitzOnWith L f (closedBall x₀ R))
    (hτ : 0<τ) (ht : |t|<τ)
    (γ η : C(TimeInterval,E))
    (hγ : γ = ContinuousMap.const TimeInterval x + t • volterra (superpose f hf γ))
    (hη : η = ContinuousMap.const TimeInterval x + τ • volterra (superpose f hf η))
    (hγball : dist γ (ContinuousMap.const TimeInterval x₀)<R)
    (hηball : dist η (ContinuousMap.const TimeInterval x₀)<R) :
    γ ⟨1,by norm_num⟩ = extendPath η (t/τ) := by
  have hratio : |t/τ|<1 := by
    rw [abs_div, abs_of_pos hτ, div_lt_one hτ]
    exact ht
  have hinner {s : ℝ} (hs : s∈Ioo (-1:ℝ) 1) : (t/τ)*s∈Ioo (-1:ℝ) 1 := by
    apply abs_lt.mp
    rw [abs_mul]
    have hsn : |s|<1 := abs_lt.mpr hs
    nlinarith [abs_nonneg (t/τ), abs_nonneg s]
  have hscaled : ∀ s∈Ioo (-1:ℝ) 1,
      HasDerivAt (fun q => extendPath η ((t/τ)*q))
        (t • f (extendPath η ((t/τ)*s))) s := by
    intro s hs
    have hd := (fixedPoint_hasDerivAt hη (hinner hs)).scomp s
      ((hasDerivAt_id s).const_mul (t/τ))
    have hev : superpose f hf η ⟨(t/τ)*s, (hinner hs).1.le, (hinner hs).2.le⟩ =
        f (extendPath η ((t/τ)*s)) := by
      rw [show extendPath η ((t/τ)*s) = η ⟨(t/τ)*s, (hinner hs).1.le,
        (hinner hs).2.le⟩ from extendPath_apply η ⟨(t/τ)*s,(hinner hs).1.le,(hinner hs).2.le⟩]
      rfl
    simpa only [Function.comp_def, id_eq, mul_one, hev, smul_smul,
      div_mul_cancel₀ t (ne_of_gt hτ)] using hd
  have hprimary : ∀s∈Ioo (-1:ℝ) 1,
      HasDerivAt (extendPath γ) (t • f (extendPath γ s)) s := by
    intro s hs
    have hev : superpose f hf γ ⟨s,hs.1.le,hs.2.le⟩ = f (extendPath γ s) := by
      rw [show extendPath γ s = γ ⟨s,hs.1.le,hs.2.le⟩ from extendPath_apply γ ⟨s,hs.1.le,hs.2.le⟩]
      rfl
    simpa only [hev] using fixedPoint_hasDerivAt hγ hs
  have hlip : LipschitzOnWith (‖t‖₊*L) (fun y => t • f y) (closedBall x₀ R) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro y hy z hz
    rw [dist_smul₀, NNReal.coe_mul, coe_nnnorm]
    exact (mul_le_mul_of_nonneg_left (hL.dist_le_mul y hy z hz) (norm_nonneg t)).trans_eq
      (by ring)
  have heq := ODE_solution_unique_of_mem_Icc
    (v:=fun _ y => t • f y) (s:=fun _ => closedBall x₀ R)
    (fun _ _ => hlip) (show (0:ℝ)∈Ioo (-1:ℝ) 1 by norm_num)
    (extendPath γ).continuous.continuousOn hprimary
    (fun s _ => ball_subset_closedBall (extendPath_mem_ball hγball s))
    (((extendPath η).continuous.comp (continuous_const.mul continuous_id)).continuousOn)
    hscaled
    (fun s _ => ball_subset_closedBall (extendPath_mem_ball hηball ((t/τ)*s)))
    (show extendPath γ 0 = extendPath η ((t/τ)*0) by
      rw [mul_zero]
      exact (extendPath_apply γ ⟨0,by norm_num⟩).trans (fixedPoint_initial hγ) |>.trans
        ((extendPath_apply η ⟨0,by norm_num⟩).trans (fixedPoint_initial hη)).symm)
  have he := heq (show (1:ℝ)∈Icc (-1:ℝ) 1 by norm_num)
  change extendPath γ 1 = extendPath η ((t/τ)*1) at he
  rw [mul_one] at he
  exact (extendPath_apply γ ⟨1,by norm_num⟩).symm.trans he

end OAI.Analysis.ODE.SmoothFlow
