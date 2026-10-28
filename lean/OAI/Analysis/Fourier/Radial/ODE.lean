import Mathlib

/-! Energy and scattering coordinates for the inverse-square perturbation of
the harmonic oscillator arising from radial Fourier kernels. -/

open Set Filter
open scoped Topology

noncomputable section
namespace OAI.Analysis.Fourier.Radial

def oscillatorEnergy (u v : ℝ → ℝ) (t : ℝ) : ℝ := u t ^ 2 + v t ^ 2

def outgoingCosine (u v : ℝ → ℝ) (t : ℝ) : ℝ :=
  u t * Real.cos t - v t * Real.sin t

def outgoingSine (u v : ℝ → ℝ) (t : ℝ) : ℝ :=
  u t * Real.sin t + v t * Real.cos t

theorem hasDerivAt_oscillatorEnergy {u v : ℝ → ℝ} {κ t : ℝ}
    (hu : HasDerivAt u (v t) t)
    (hv : HasDerivAt v ((κ / t ^ 2 - 1) * u t) t) :
    HasDerivAt (oscillatorEnergy u v) (2 * κ / t ^ 2 * u t * v t) t := by
  unfold oscillatorEnergy
  convert (hu.pow 2).add (hv.pow 2) using 1 ; ring

theorem oscillatorEnergy_deriv_bound (κ t U V : ℝ) :
    |2 * κ / t ^ 2 * U * V| ≤ |κ| / t ^ 2 * (U ^ 2 + V ^ 2) := by
  have h : |2 * U * V| ≤ U ^ 2 + V ^ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (U - V), sq_nonneg (U + V)]
  calc
    _ = |κ| / t ^ 2 * |2 * U * V| := by
      rw [show 2 * κ / t ^ 2 * U * V = (κ / t ^ 2) * (2 * U * V) by ring,
        abs_mul, abs_div, abs_of_nonneg (sq_nonneg t)]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

theorem hasDerivAt_outgoingCosine {u v : ℝ → ℝ} {κ t : ℝ}
    (hu : HasDerivAt u (v t) t)
    (hv : HasDerivAt v ((κ / t ^ 2 - 1) * u t) t) :
    HasDerivAt (outgoingCosine u v) (-κ / t ^ 2 * u t * Real.sin t) t := by
  unfold outgoingCosine
  convert (hu.mul (Real.hasDerivAt_cos t)).sub (hv.mul (Real.hasDerivAt_sin t)) using 1 ; ring

theorem hasDerivAt_outgoingSine {u v : ℝ → ℝ} {κ t : ℝ}
    (hu : HasDerivAt u (v t) t)
    (hv : HasDerivAt v ((κ / t ^ 2 - 1) * u t) t) :
    HasDerivAt (outgoingSine u v) (κ / t ^ 2 * u t * Real.cos t) t := by
  unfold outgoingSine
  convert (hu.mul (Real.hasDerivAt_sin t)).add (hv.mul (Real.hasDerivAt_cos t)) using 1 ; ring

theorem outgoing_energy (u v : ℝ → ℝ) (t : ℝ) :
    outgoingCosine u v t ^ 2 + outgoingSine u v t ^ 2 = oscillatorEnergy u v t := by
  have h := Real.sin_sq_add_cos_sq t
  dsimp [outgoingCosine, outgoingSine, oscillatorEnergy]
  nlinarith [sq_nonneg (u t), sq_nonneg (v t)]

theorem outgoing_reconstruct (u v : ℝ → ℝ) (t : ℝ) :
    u t = outgoingCosine u v t * Real.cos t + outgoingSine u v t * Real.sin t ∧
    v t = -outgoingCosine u v t * Real.sin t + outgoingSine u v t * Real.cos t := by
  have h := Real.sin_sq_add_cos_sq t
  have hU := congrArg (fun z => u t * z) h
  have hV := congrArg (fun z => v t * z) h
  dsimp [outgoingCosine, outgoingSine]
  constructor <;> nlinarith [hU, hV]

theorem hasDerivAt_exp_inv_mul {F : ℝ → ℝ} {d t : ℝ}
    (hF : HasDerivAt F d t) (ht : t ≠ 0) (c : ℝ) :
    HasDerivAt (fun r => Real.exp (c / r) * F r)
      (Real.exp (c / t) * (d - c / t ^ 2 * F t)) t := by
  have hq := (hasDerivAt_const t c).div (hasDerivAt_id t) ht
  change HasDerivAt (fun r : ℝ => c / r) ((0 * t - c * 1) / t ^ 2) t at hq
  have H := hq.exp.mul hF
  change HasDerivAt (fun r => Real.exp (c / r) * F r)
    ((Real.exp (c / t) * ((0 * t - c * 1) / t ^ 2)) * F t + Real.exp (c / t) * d) t at H
  convert H using 1 ; ring

theorem inverseSquare_energy_bounds {F d : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hF : ∀ t, 1 ≤ t → HasDerivAt F (d t) t)
    (hpos : ∀ t, 1 ≤ t → 0 ≤ F t)
    (hd : ∀ t, 1 ≤ t → |d t| ≤ c / t ^ 2 * F t) :
    ∀ r, 1 ≤ r → Real.exp (-c) * F 1 ≤ F r ∧ F r ≤ Real.exp c * F 1 := by
  let P := fun r => Real.exp (c / r) * F r
  let Q := fun r => Real.exp (-c / r) * F r
  have hP (r : ℝ) (hr : 1 ≤ r) :=
    hasDerivAt_exp_inv_mul (hF r hr) (by linarith : r ≠ 0) c
  have hQ (r : ℝ) (hr : 1 ≤ r) :=
    hasDerivAt_exp_inv_mul (hF r hr) (by linarith : r ≠ 0) (-c)
  have hpm : AntitoneOn P (Ici 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
      (fun r hr => (hP r hr).continuousAt.continuousWithinAt)
    · intro r hr
      rw [interior_Ici] at hr
      exact (hP r hr.le).differentiableAt.differentiableWithinAt
    · intro r hr
      rw [interior_Ici] at hr
      rw [(hP r hr.le).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (sub_nonpos.mpr ((le_abs_self _).trans (hd r hr.le)))
  have hqm : MonotoneOn Q (Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
      (fun r hr => (hQ r hr).continuousAt.continuousWithinAt)
    · intro r hr
      rw [interior_Ici] at hr
      exact (hQ r hr.le).differentiableAt.differentiableWithinAt
    · intro r hr
      rw [interior_Ici] at hr
      rw [(hQ r hr.le).deriv]
      apply mul_nonneg (Real.exp_pos _).le
      have H := (neg_le_abs (d r)).trans (hd r hr.le)
      simp only [neg_div, neg_mul, sub_neg_eq_add]
      linarith
  intro r hr
  have hrp : 0 < r := by linarith
  have HP : P r ≤ Real.exp c * F 1 := by simpa [P] using hpm (by simp) hr hr
  have HQ : Real.exp (-c) * F 1 ≤ Q r := by simpa [Q] using hqm (by simp) hr hr
  constructor
  · apply HQ.trans
    have he : Real.exp (-c / r) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) hrp.le)
    dsimp [Q]
    nlinarith [hpos r hr]
  · apply le_trans _ HP
    have he : 1 ≤ Real.exp (c / r) := Real.one_le_exp_iff.mpr (div_nonneg hc hrp.le)
    dsimp [P]
    nlinarith [hpos r hr]

theorem oscillatorEnergy_bounds {u v : ℝ → ℝ} {κ : ℝ}
    (hu : ∀ t, 1 ≤ t → HasDerivAt u (v t) t)
    (hv : ∀ t, 1 ≤ t → HasDerivAt v ((κ / t ^ 2 - 1) * u t) t) :
    ∀ r, 1 ≤ r →
      Real.exp (-|κ|) * oscillatorEnergy u v 1 ≤ oscillatorEnergy u v r ∧
      oscillatorEnergy u v r ≤ Real.exp |κ| * oscillatorEnergy u v 1 := by
  apply inverseSquare_energy_bounds (abs_nonneg κ)
  · intro t ht
    exact hasDerivAt_oscillatorEnergy (hu t ht) (hv t ht)
  · intro t ht
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  · intro t ht
    exact oscillatorEnergy_deriv_bound κ t (u t) (v t)

end OAI.Analysis.Fourier.Radial
