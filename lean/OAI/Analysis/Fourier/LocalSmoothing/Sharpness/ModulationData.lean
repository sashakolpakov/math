import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.ModulationPhase

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Filter
open scoped Topology ENNReal
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

theorem temperate_modulation {n : ℕ} (v : Space n) :
    (fun x : Space n => Complex.exp (Complex.I * (inner ℝ x v : ℂ))).HasTemperateGrowth := by
  have hi : (fun x : Space n => inner ℝ x v).HasTemperateGrowth := by
    have he : (⇑(innerSL ℝ v) : Space n → ℝ) = fun x => inner ℝ x v := by
      ext x
      simp only [innerSL_apply_apply,real_inner_comm]
    rw [← he]
    exact (innerSL ℝ v).hasTemperateGrowth
  simpa only [Function.comp_def,mul_comm] using Complex.hasTemperateGrowth_exp_mul_I.comp hi

def schwartzModulation {n : ℕ} (v : Space n) (f : SchwartzMap (Space n) ℂ) :
    SchwartzMap (Space n) ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x => Complex.exp (Complex.I * (inner ℝ x v : ℂ))) f

@[simp] theorem schwartzModulation_apply {n : ℕ} (v : Space n)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    schwartzModulation v f x = Complex.exp (Complex.I * (inner ℝ x v : ℂ)) * f x := by
  rw [schwartzModulation,SchwartzMap.smulLeftCLM_apply_apply (temperate_modulation v)]
  rfl

theorem schwartzModulation_eq_restrictionModulate {n : ℕ} (v : Space n)
    (f : SchwartzMap (Space n) ℂ) :
    (schwartzModulation v f : Space n → ℂ) = OAI.Analysis.Fourier.Restriction.restrictionModulate (-v) f := by
  funext x
  simp only [schwartzModulation_apply,OAI.Analysis.Fourier.Restriction.restrictionModulate,inner_neg_right,
    Complex.ofReal_neg,neg_mul_neg]

theorem angularFourier_schwartzModulation {n : ℕ} (v : Space n)
    (f : SchwartzMap (Space n) ℂ) (ξ : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier (schwartzModulation v f) ξ = OAI.Analysis.Fourier.LocalSmoothing.angularFourier f (ξ-v) := by
  rw [schwartzModulation_eq_restrictionModulate,OAI.Analysis.Fourier.Restriction.angularFourier_restrictionModulate]
  rfl

theorem norm_schwartzModulation {n : ℕ} (v : Space n)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    ‖schwartzModulation v f x‖ = ‖f x‖ := by
  rw [schwartzModulation_eq_restrictionModulate]
  exact OAI.Analysis.Fourier.Restriction.norm_restrictionModulate (-v) f x

theorem eLpNorm_schwartzModulation {n : ℕ} (v : Space n)
    (f : SchwartzMap (Space n) ℂ) (p : ℝ≥0∞) :
    eLpNorm (schwartzModulation v f) p volume = eLpNorm f p volume := by
  rw [schwartzModulation_eq_restrictionModulate]
  exact OAI.Analysis.Fourier.Restriction.eLpNorm_restrictionModulate (-v) f.continuous.measurable p

theorem schwartzModulation_annular_support {n : ℕ} {N : ℝ} (hN : 4 ≤ N)
    {ω : Space n} (hω : ‖ω‖ = 1) (f : SchwartzMap (Space n) ℂ)
    (hf : ∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → ‖ξ‖ ≤ 2) :
    ∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier (schwartzModulation ((3*N/2) • ω) f) ξ ≠ 0 →
      N ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2*N := by
  intro ξ hξ
  rw [angularFourier_schwartzModulation] at hξ
  have hsmall := hf _ hξ
  have hv : ‖(3*N/2) • ω‖ = 3*N/2 := by
    rw [norm_smul,hω,mul_one,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
  have hlo := norm_sub_le ξ (ξ - (3*N/2) • ω)
  have hhi := norm_add_le (ξ - (3*N/2) • ω) ((3*N/2) • ω)
  rw [sub_sub_cancel,hv] at hlo
  rw [sub_add_cancel,hv] at hhi
  constructor <;> linarith

/-- The modulated bump has Sobolev norm at most a constant times N^s,
for every real s, including the negative orders ruled out by sharpness. -/
theorem schwartzModulation_bessel_bound (n : ℕ) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℝ, 4 ≤ N → ∀ ω : Space n, ‖ω‖ = 1 →
      ∀ f : SchwartzMap (Space n) ℂ,
      (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → ‖ξ‖ ≤ 2) →
      ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.besselPotential s (schwartzModulation ((3*N/2) • ω) f)) p volume ≤
        ENNReal.ofReal (C * N^s) * eLpNorm f p volume := by
  obtain ⟨C,hC,hb⟩ := sharpness_annular_bessel_bound n s
  refine ⟨C,hC,?_⟩
  intro N hN ω hω f hf p hp hptop
  simpa only [eLpNorm_schwartzModulation] using
    hb N hN (schwartzModulation ((3*N/2) • ω) f)
      (schwartzModulation_annular_support hN hω f hf) p hp hptop

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
