import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.RadialData
import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.PhaseIntegral
import OAI.Analysis.Fourier.Restriction.SmoothInverse

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

open Set Metric Filter _root_.MeasureTheory
open scoped Topology ContDiff

def radialSymbol (n : ℕ) (ξ : Space n) : ℂ := (radialBump ‖ξ‖ : ℝ)

theorem radialSymbol_support (n : ℕ) :
    tsupport (radialSymbol n) ⊆ {ξ | 1 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2} := by
  apply closure_minimal ?_ ((isClosed_le continuous_const continuous_norm).inter
    (isClosed_le continuous_norm continuous_const))
  intro ξ hξ
  apply radialBump_support
  apply subset_tsupport (radialBump : ℝ → ℝ)
  intro he
  apply hξ
  simp only [radialSymbol,he,Complex.ofReal_zero]

theorem radialSymbol_zero_notMem (n : ℕ) : (0 : Space n) ∉ tsupport (radialSymbol n) := by
  intro h
  have := (radialSymbol_support n h).1
  simpa using (not_le_of_gt (show (0:ℝ)<1 by norm_num)) (by simpa using this)

theorem radialSymbol_hasCompactSupport (n : ℕ) : HasCompactSupport (radialSymbol n) := by
  apply (isCompact_closedBall (0 : Space n) 2).of_isClosed_subset (isClosed_tsupport _)
  intro ξ hξ
  simpa only [mem_closedBall,dist_zero_right] using (radialSymbol_support n hξ).2

theorem radialSymbol_contDiff (n : ℕ) : ContDiff ℝ ∞ (radialSymbol n) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases hξ : ξ = 0
  · subst ξ
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    exact notMem_tsupport_iff_eventuallyEq.mp (radialSymbol_zero_notMem n)
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp ξ
      (radialBump.contDiff.contDiffAt.comp ξ (contDiffAt_id.norm ℝ hξ))

def focusingSymbol (n : ℕ) (N t₀ : ℝ) (ξ : Space n) : ℂ :=
  phase (t₀*‖ξ‖) * radialSymbol n (N⁻¹ • ξ)

theorem focusingSymbol_hasCompactSupport (n : ℕ) {N : ℝ} (hN : N ≠ 0) (t₀ : ℝ) :
    HasCompactSupport (focusingSymbol n N t₀) :=
  ((radialSymbol_hasCompactSupport n).comp_smul (inv_ne_zero hN)).mul_left

theorem focusingSymbol_contDiff (n : ℕ) {N : ℝ} (_ : N ≠ 0) (t₀ : ℝ) :
    ContDiff ℝ ∞ (focusingSymbol n N t₀) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  have hs : ContDiff ℝ ∞ (fun ξ : Space n => radialSymbol n (N⁻¹ • ξ)) :=
    (radialSymbol_contDiff n).comp (by fun_prop)
  by_cases hξ : ξ = 0
  · subst ξ
    have hz : ∀ᶠ x in 𝓝 (0:Space n), radialSymbol n (N⁻¹ • x) = 0 :=
      (notMem_tsupport_iff_eventuallyEq.mp (radialSymbol_zero_notMem n)).comp_tendsto
        ((by fun_prop : Continuous (fun x : Space n => N⁻¹ • x)).tendsto' 0 0 (smul_zero _))
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    filter_upwards [hz] with x hx
    simp only [focusingSymbol,hx,mul_zero]
  · have hphase : ContDiffAt ℝ ∞ (fun ξ : Space n => phase (t₀*‖ξ‖)) ξ := by
      unfold phase
      exact (Complex.contDiff_exp.contDiffAt.comp _
        (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp _
          (contDiffAt_const.mul (contDiffAt_id.norm ℝ hξ)))))
    exact hphase.mul hs.contDiffAt

/-- The focusing examples are actual Schwartz functions with the exact
prescribed angular Fourier transform. -/
theorem exists_focusing_packet (n : ℕ) {N : ℝ} (hN : N ≠ 0) (t₀ : ℝ) :
    ∃ f : SchwartzMap (Space n) ℂ,
      (f : Space n → ℂ) = OAI.Analysis.Fourier.LocalSmoothing.angularInverse (focusingSymbol n N t₀) ∧
      ∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ = focusingSymbol n N t₀ ξ :=
  OAI.Analysis.Fourier.Restriction.exists_schwartz_angularInverse_pair
    (focusingSymbol_contDiff n hN t₀) (focusingSymbol_hasCompactSupport n hN t₀)

theorem focusing_packet_annular {n : ℕ} {N t₀ : ℝ} (hN : 0 < N)
    {f : SchwartzMap (Space n) ℂ}
    (hf : ∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ = focusingSymbol n N t₀ ξ) :
    ∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → N ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2*N := by
  intro ξ hξ
  rw [hf] at hξ
  have hs : N⁻¹ • ξ ∈ tsupport (radialSymbol n) :=
    subset_tsupport _ (right_ne_zero_of_mul hξ)
  have hbounds := radialSymbol_support n hs
  change 1 ≤ ‖N⁻¹ • ξ‖ ∧ ‖N⁻¹ • ξ‖ ≤ 2 at hbounds
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hN)] at hbounds
  constructor <;> nlinarith [mul_inv_cancel₀ hN.ne']

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
