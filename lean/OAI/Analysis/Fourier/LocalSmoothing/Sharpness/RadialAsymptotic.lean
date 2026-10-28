import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.Sphere
import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.PhaseIntegral
import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.RadialData

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff

def radialOrder (n : ℕ) : ℝ := ((n : ℝ)-1)/2

def normalizedSphere (n : ℕ) (x : Space n) : ℂ :=
  (‖x‖ ^ radialOrder n : ℝ) *
    OAI.Analysis.Fourier.Restriction.sphericalExtension (fun _ : Space n => (1:ℂ)) x

theorem continuous_normalizedSphere {n : ℕ} (hn : 1 ≤ n) :
    Continuous (normalizedSphere n) := by
  have hm : 0 ≤ radialOrder n := by
    have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
    dsimp [radialOrder]
    linarith
  have hc : Continuous (fun x : Space n => ‖x‖ ^ radialOrder n) :=
    (Real.continuous_rpow_const hm).comp continuous_norm
  exact (Complex.continuous_ofReal.comp hc).mul
    (OAI.Analysis.Fourier.Restriction.continuous_sphericalExtension (integrable_const _))

def normalizedRadialWave (n : ℕ) (g : ℝ → ℝ) (t : ℝ) (x : Space n) : ℂ :=
  ∫ σ : ℝ, phase (-t*σ)*(g σ:ℂ)*normalizedSphere n (σ • x)

theorem normalizedRadialWave_expansion {n : ℕ} (hn : 1 ≤ n)
    {g : ℝ → ℝ} (hg : Continuous g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ Icc 1 2) :
    ∃ c : ℂ, c ≠ 0 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ∀ x : Space n, 1 ≤ ‖x‖ →
      ‖normalizedRadialWave n g t x -
        (c*radialProfile g (‖x‖-t)+star c*radialProfile g (-(‖x‖+t)))‖ ≤
          C/‖x‖ := by
  obtain ⟨c,hc0,C,hC,hsp⟩ := sphere_two_phase_asymptotic hn
  refine ⟨c,hc0,C*(∫ σ,‖g σ‖),mul_nonneg hC (integral_nonneg (fun _ => norm_nonneg _)),?_⟩
  intro t x hx
  have hr : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hx
  have he := integral_two_phase_error hg hc
    ((continuous_normalizedSphere hn).comp (by fun_prop : Continuous (fun σ : ℝ => σ • x)))
    c ‖x‖ t (C/‖x‖) (div_nonneg hC hr.le) (fun σ hσ => by
      have hσ1 := (hs hσ).1
      have hσ0 : 0 ≤ σ := le_trans zero_le_one hσ1
      have hnorm : ‖σ • x‖ = σ*‖x‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hσ0]
      have hle : ‖x‖ ≤ σ*‖x‖ := by nlinarith
      have h1 : 1 ≤ ‖σ • x‖ := by rw [hnorm]; exact hx.trans hle
      have hh := hsp (σ • x) h1
      change ‖normalizedSphere n (σ • x) -
        (c*phase (‖σ • x‖)+star c*Complex.exp (-Complex.I*(‖σ • x‖:ℂ)))‖ ≤ C/‖σ • x‖ at hh
      have hphase : Complex.exp (-Complex.I*(‖σ • x‖:ℂ)) = phase (-‖σ • x‖) := by
        unfold phase
        congr 1
        push_cast
        ring
      rw [hphase] at hh
      have heq : ‖σ • x‖ = ‖x‖*σ := by rw [hnorm,mul_comm]
      rw [heq] at hh
      simpa only [neg_mul,Function.comp_def] using!
        hh.trans (div_le_div_of_nonneg_left hC hr (by nlinarith)))
  change ‖normalizedRadialWave n g t x -
    (c*radialProfile g (‖x‖-t)+star c*radialProfile g (-(‖x‖+t)))‖ ≤
      C/‖x‖*(∫ σ,‖g σ‖) at he
  convert he using 1 ; ring

theorem outgoing_norm_lower (W U V : ℂ) {a e : ℝ}
    (hU : a ≤ ‖U‖) (hV : ‖V‖ ≤ e) (hW : ‖W-(U+V)‖ ≤ e) :
    a-2*e ≤ ‖W‖ := by
  have hu := norm_sub_le (U+V) V
  rw [add_sub_cancel_right] at hu
  have hw := norm_sub_le W (W-(U+V))
  rw [sub_sub_cancel] at hw
  linarith

/-- A concrete positive smooth radial amplitude has a uniform nonzero
outgoing shell once its radius is sufficiently large. -/
theorem normalizedRadialWave_shell_lower {n : ℕ} (hn : 1 ≤ n) :
    ∃ η k R : ℝ, 0 < η ∧ 0 < k ∧ 1 ≤ R ∧ ∀ t : ℝ, ∀ x : Space n,
      R ≤ ‖x‖ → |‖x‖-t| ≤ η →
      k ≤ ‖normalizedRadialWave n (weightedRadialBump (radialOrder n)) t x‖ := by
  let g := weightedRadialBump (radialOrder n)
  obtain ⟨η,c0,hη,hc0,hnear,hfar⟩ := weightedRadialBump_profile (radialOrder n)
  obtain ⟨c,hc,C,hC,herror⟩ := normalizedRadialWave_expansion hn
    (weightedRadialBump_contDiff _).continuous (weightedRadialBump_hasCompactSupport _)
    (weightedRadialBump_support _)
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  let a := ‖c‖*c0
  have ha : 0 < a := mul_pos hcn hc0
  have hevent : ∀ᶠ s : ℝ in atTop, ‖radialProfile g (-s)‖ < c0/4 := by
    exact (hfar.norm).eventually (gt_mem_nhds (by simpa using (show 0 < c0/4 by positivity)))
  obtain ⟨M,hM⟩ := eventually_atTop.1 hevent
  let R := max 2 (max (M+1) (4*C/a))
  refine ⟨min η 1,a/2,R,lt_min hη zero_lt_one,half_pos ha,
    (by dsimp [R]; exact le_trans (by norm_num) (le_max_left _ _)),?_⟩
  intro t x hx hxt
  have hR2 : 2 ≤ ‖x‖ := (le_max_left _ _).trans hx
  have hRM : M+1 ≤ ‖x‖ := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hx
  have hRC : 4*C/a ≤ ‖x‖ := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hx
  have hr : 0 < ‖x‖ := by linarith
  have hnear' := hnear (‖x‖-t) (hxt.trans (min_le_left _ _))
  have hclose : ‖x‖-t ≤ 1 := (le_abs_self _).trans (hxt.trans (min_le_right _ _))
  have hMsum : M ≤ ‖x‖+t := by linarith
  have hinc : ‖star c*radialProfile g (-(‖x‖+t))‖ ≤ a/4 := by
    rw [norm_mul,norm_star]
    have := mul_le_mul_of_nonneg_left (hM (‖x‖+t) hMsum).le hcn.le
    dsimp [a]
    nlinarith
  have herr : ‖normalizedRadialWave n g t x -
      (c*radialProfile g (‖x‖-t)+star c*radialProfile g (-(‖x‖+t)))‖ ≤ a/4 := by
    apply (herror t x (by linarith)).trans
    apply (div_le_iff₀ hr).2
    have := (div_le_iff₀ ha).1 hRC
    nlinarith
  have hout : a ≤ ‖c*radialProfile g (‖x‖-t)‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hnear' hcn.le
  have hh := outgoing_norm_lower _ _ _ hout hinc herr
  convert hh using 1 ; ring

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
