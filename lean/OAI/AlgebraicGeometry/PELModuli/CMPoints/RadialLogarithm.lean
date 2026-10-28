import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Radial Logarithm -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.RadialLogarithm

noncomputable section

/-! The actual local inverse is recovered by integrating its vertical
derivative along a radial segment. This lets a family logarithm be
compared with an integral of the invariant differential. -/

open Set _root_.Metric Filter
open scoped _root_.Topology

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace V] in
theorem local_inverse_hasFDerivAt
    (f g : V → V) (D : V → V ≃L[ℝ] V) (U : Set V) (hU : IsOpen U)
    (hg : ContinuousOn g U)
    (hf : ∀ y ∈ U, HasFDerivAt f (D y).toContinuousLinearMap (g y))
    (hinv : ∀ y ∈ U, f (g y) = y) (y : V) (hy : y ∈ U) :
    HasFDerivAt g (D y).symm.toContinuousLinearMap y := by
  exact (hf y hy).of_local_left_inverse (hg.continuousAt (hU.mem_nhds hy))
    (Filter.mem_of_superset (hU.mem_nhds hy) (fun z hz => hinv z hz))

theorem local_inverse_eq_radial_integral
    (f g : V → V) (D : V → V ≃L[ℝ] V) (r : ℝ)
    (hg : ContinuousOn g (ball 0 r))
    (hf : ∀ y ∈ ball 0 r, HasFDerivAt f (D y).toContinuousLinearMap (g y))
    (hinv : ∀ y ∈ ball 0 r, f (g y) = y) (hzero : g 0 = 0)
    (hD : ContinuousOn (fun y => (D y).symm.toContinuousLinearMap) (ball 0 r))
    (y : V) (hy : y ∈ ball 0 r) :
    g y = ∫ t : ℝ in 0..1, (D (t • y)).symm y := by
  have hsegment : MapsTo (fun t : ℝ => t • y) (uIcc 0 1) (ball 0 r) := by
    intro t ht
    have ht' : 0 ≤ t ∧ t ≤ 1 := by simpa only [uIcc_of_le zero_le_one, mem_Icc] using ht
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht'.1]
    exact (mul_le_of_le_one_left (norm_nonneg y) ht'.2).trans_lt
      (by simpa only [mem_ball, dist_zero_right] using hy)
  have hd (t : ℝ) (ht : t ∈ uIcc 0 1) :
      HasDerivAt (fun t : ℝ => g (t • y)) ((D (t • y)).symm y) t := by
    simpa only [Function.comp_def, id_eq, one_smul, ContinuousLinearEquiv.coe_coe] using
      (local_inverse_hasFDerivAt f g D (ball 0 r) isOpen_ball hg hf hinv _
        (hsegment ht)).comp_hasDerivAt t ((hasDerivAt_id t).smul_const y)
  have hcont : ContinuousOn (fun t : ℝ => (D (t • y)).symm y) (uIcc 0 1) :=
    ((hD.comp (continuous_id.smul continuous_const).continuousOn hsegment).clm_apply
      continuousOn_const)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable
  simpa only [one_smul, zero_smul, hzero, sub_zero] using h.symm

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.RadialLogarithm
