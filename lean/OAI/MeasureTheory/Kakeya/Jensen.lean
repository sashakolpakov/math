import OAI.MeasureTheory.Kakeya.MaximalDiscrete

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal

noncomputable section
namespace OAI.MeasureTheory.Kakeya

/-- The power-mean inequality for an arbitrary nonzero finite measure,
written with the normalized integrals used in tube averages. -/
theorem lintegral_average_enorm_rpow_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : AEStronglyMeasurable f μ) (hμ : μ Set.univ ≠ 0) (hμ' : μ Set.univ ≠ ∞)
    {r : ℝ} (hr : 1 ≤ r) :
    ((∫⁻ x, ‖f x‖ₑ ∂μ) / μ Set.univ) ^ r ≤
      (∫⁻ x, ‖f x‖ₑ ^ r ∂μ) / μ Set.univ := by
  let ν : Measure α := (μ Set.univ)⁻¹ • μ
  have : IsProbabilityMeasure ν := ⟨by
    simp only [ν, Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hμ hμ']⟩
  have hm : AEStronglyMeasurable f ν := hf.smul_measure _
  have hrpos : 0 < r := by linarith
  have h := eLpNorm_le_eLpNorm_of_exponent_le (f := f) (μ := ν)
    (ENNReal.one_le_ofReal.mpr hr)
  rw [eLpNorm_one_eq_lintegral_enorm hm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hm,
    ENNReal.toReal_ofReal hrpos.le] at h
  have hp := ENNReal.rpow_le_rpow h hrpos.le
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hrpos.ne', ENNReal.rpow_one] at hp
  simpa only [ν, lintegral_smul_measure, smul_eq_mul, div_eq_mul_inv, mul_comm] using hp

def kakeyaPowerInput {n : ℕ} (r : ℝ) (f : Space n → ℂ) (x : Space n) : ℂ :=
  (‖f x‖ ^ r : ℝ)

theorem norm_kakeyaPowerInput {n : ℕ} (r : ℝ) (f : Space n → ℂ) (x : Space n) :
    ‖kakeyaPowerInput r f x‖ = ‖f x‖ ^ r := by
  simp [kakeyaPowerInput, Real.rpow_nonneg (norm_nonneg _)]

theorem enorm_kakeyaPowerInput {n : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (f : Space n → ℂ) (x : Space n) :
    ‖kakeyaPowerInput r f x‖ₑ = ‖f x‖ₑ ^ r := by
  rw [← ofReal_norm, norm_kakeyaPowerInput, ← ofReal_norm,
    ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr]

theorem memLp_kakeyaPowerInput {n : ℕ} {p r : ℝ} (hp : 0 < p) (hr : 0 < r)
    {f : Space n → ℂ} (hf : MemLp f (ENNReal.ofReal (p * r)) volume) :
    MemLp (kakeyaPowerInput r f) (ENNReal.ofReal p) volume := by
  have h : MemLp (fun x : Space n ↦ ((‖f x‖ ^ (ENNReal.ofReal r).toReal : ℝ) : ℂ))
      (ENNReal.ofReal (p * r) / ENNReal.ofReal r) (volume : Measure (Space n)) :=
    (hf.norm_rpow_div (ENNReal.ofReal r)).ofReal (K := ℂ)
  change MemLp (fun x : Space n ↦ ((‖f x‖ ^ r : ℝ) : ℂ)) (ENNReal.ofReal p)
    (volume : Measure (Space n))
  simpa only [ENNReal.toReal_ofReal hr.le,
    ENNReal.ofReal_mul hp.le, ENNReal.mul_div_cancel_right (by positivity : ENNReal.ofReal r ≠ 0)
      ENNReal.ofReal_ne_top] using h

theorem kakeyaMaximal_rpow_le_powerInput {n : ℕ} {δ r : ℝ}
    (hδ : 0 < δ) (hr : 1 ≤ r) {f : Space n → ℂ}
    (hf : AEStronglyMeasurable f (volume : Measure (Space n))) (ω : Space n) :
    OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f ω ^ r ≤ OAI.MeasureTheory.Kakeya.kakeyaMaximal δ (kakeyaPowerInput r f) ω := by
  have hrpos : 0 < r := by linarith
  rw [OAI.MeasureTheory.Kakeya.kakeyaMaximal, ennreal_rpow_iSup _ hrpos]
  apply iSup_le
  intro x
  have h := lintegral_average_enorm_rpow_le
    (hf.mono_measure Measure.restrict_le_self)
    (μ := volume.restrict (OAI.MeasureTheory.Kakeya.tube δ ω x))
    (by simpa using (volume_tube_pos hδ ω x).ne')
    (by simpa using (volume_tube_lt_top δ ω x).ne) hr
  have heq : (fun y ↦ ‖f y‖ₑ ^ r) = fun y ↦ ‖kakeyaPowerInput r f y‖ₑ := by
    funext y
    exact (enorm_kakeyaPowerInput hrpos.le f y).symm
  rw [heq, Measure.restrict_apply_univ] at h
  exact h.trans (le_iSup (fun z : Space n ↦
    (∫⁻ y in OAI.MeasureTheory.Kakeya.tube δ ω z, ‖kakeyaPowerInput r f y‖ₑ) / volume (OAI.MeasureTheory.Kakeya.tube δ ω z)) x)

end OAI.MeasureTheory.Kakeya
