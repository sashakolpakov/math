import OAI.NumberTheory.Quaternion.Arithmetic.LocalCompletion
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! # Local Exp Derivative -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.LocalExpDerivative

noncomputable section

/-! The derivative of an exponential curve inside its actual convergence
disk. The argument uses the addition formula and the derivative at zero. -/

open scoped Classical
open NormedSpace Filter _root_.Topology

variable {K A : Type*} [NontriviallyNormedField K] [CharZero K]
  [NormedRing A] [NormedAlgebra K A] [CompleteSpace A]

omit [CharZero K] [CompleteSpace A] in
theorem local_exp_smul_eventually_mem_ball (hr : 0 < (expSeries K A).radius) (X : A) :
    ∀ᶠ t : K in 𝓝 0, t • X ∈ Metric.eball 0 (expSeries K A).radius := by
  have hc : ContinuousAt (fun t : K => t • X) 0 :=
    (continuous_id.smul continuous_const).continuousAt
  apply hc.preimage_mem_nhds
  simpa only [zero_smul] using Metric.eball_mem_nhds (0 : A) hr

theorem local_exp_hasFDerivAt_zero (hr : 0 < (expSeries K A).radius) :
    HasFDerivAt (exp : A → A) (ContinuousLinearMap.id K A) 0 := by
  have h := (hasFPowerSeriesAt_exp_zero_of_radius_pos hr).hasFDerivAt
  have he : continuousMultilinearCurryFin1 K A A (expSeries K A 1) =
      ContinuousLinearMap.id K A := by
    ext X
    simp [expSeries]
  rwa [he] at h

theorem local_exp_smul_hasDerivAt (hr : 0 < (expSeries K A).radius)
    (X : A) (t : K) (ht : t • X ∈ Metric.eball 0 (expSeries K A).radius) :
    HasDerivAt (fun s : K => exp (s • X)) (exp (t • X) * X) t := by
  have hs : HasDerivAt (fun s : K => (s - t) • X) X t := by
    simpa using ((hasDerivAt_id t).sub_const t).smul_const X
  have he : HasDerivAt (fun s : K => exp ((s - t) • X)) X t := by
    have h0 : HasFDerivAt (exp : A → A) (ContinuousLinearMap.id K A) ((t - t) • X) := by
      simpa only [sub_self, zero_smul] using local_exp_hasFDerivAt_zero hr
    exact h0.comp_hasDerivAt t hs
  have hm := he.const_mul (exp (t • X))
  apply hm.congr_of_eventuallyEq
  have hz : (0 : A) ∈ Metric.eball 0 (expSeries K A).radius := by simpa using hr
  have hnear : ∀ᶠ s : K in 𝓝 t, (s - t) • X ∈ Metric.eball 0 (expSeries K A).radius :=
    hs.continuousAt.preimage_mem_nhds (by simpa using Metric.isOpen_eball.mem_nhds hz)
  filter_upwards [hnear] with s hs
  have hcomm : Commute (t • X) ((s - t) • X) :=
    ((Commute.refl X).smul_left t).smul_right (s - t)
  have hsum : t • X + (s - t) • X = s • X := by
    rw [← add_smul, add_sub_cancel]
  simpa only [hsum] using exp_add_of_commute_of_mem_ball hcomm ht hs

end

end OAI.NumberTheory.Quaternion.Arithmetic.LocalExpDerivative
