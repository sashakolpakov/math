import OAI.Analysis.Fourier.Cone.Measure

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Cone

theorem cone_unweighted_le (n : ℕ) :
    coneRadialMeasure.prod (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤ coneParameterMeasure n := by
  have hr : ∀ᵐ ρ ∂coneRadialMeasure, ρ ∈ Icc (1 : ℝ) 2 := ae_restrict_mem measurableSet_Icc
  calc
    _ = (coneRadialMeasure.prod (OAI.Analysis.Fourier.Restriction.sphereMeasure n)).withDensity 1 := withDensity_one.symm
    _ ≤ coneParameterMeasure n := by
      apply withDensity_mono
      filter_upwards [Measure.quasiMeasurePreserving_fst.ae hr] with p hp
      simpa using ENNReal.ofReal_le_ofReal (coneAreaWeight_bounds n hp).1

def coneData {n : ℕ} (g : Space n × ℝ → ℂ) (p : ℝ × Space n) : ℂ :=
  (coneAreaWeight n p.1 : ℂ) * g (coneParam p)

theorem measurable_coneData {n : ℕ} {g : Space n × ℝ → ℂ} (hg : Measurable g) :
    Measurable (coneData g) := by
  exact ((Complex.continuous_ofReal.comp
    ((continuous_coneAreaWeight n).comp continuous_fst)).measurable).mul
      (hg.comp (continuous_coneParam n).measurable)

theorem coneData_norm_bound {n : ℕ} (g : Space n × ℝ → ℂ) {p : ℝ × Space n}
    (hp : p.1 ∈ Icc (1 : ℝ) 2) :
    ‖coneData g p‖ ≤ (Real.sqrt 2 * 2 ^ (n - 1)) * ‖g (coneParam p)‖ := by
  rw [coneData, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (coneAreaWeight_nonneg _ _)]
  exact mul_le_mul_of_nonneg_right (coneAreaWeight_bounds n hp).2 (norm_nonneg _)

theorem coneData_lp_bound {n : ℕ} {g : Space n × ℝ → ℂ} {p : ℝ≥0∞}
    (hgm : Measurable g) (hg : MemLp g p (coneMeasure n)) :
    MemLp (coneData g) p (coneRadialMeasure.prod (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) ∧
    eLpNorm (coneData g) p (coneRadialMeasure.prod (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) ≤
      ENNReal.ofReal (Real.sqrt 2 * 2 ^ (n - 1)) * eLpNorm g p (coneMeasure n) := by
  have hcp := (continuous_coneParam n).measurable
  have hpull : MemLp (g ∘ coneParam) p (coneParameterMeasure n) :=
    (memLp_map_measure_iff hgm.aestronglyMeasurable hcp.aemeasurable).mp hg
  have hu := hpull.mono_measure (cone_unweighted_le n)
  have hm : AEStronglyMeasurable (coneData g) (coneRadialMeasure.prod (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) :=
    (measurable_coneData hgm).aestronglyMeasurable
  have hr : ∀ᵐ ρ ∂coneRadialMeasure, ρ ∈ Icc (1 : ℝ) 2 := ae_restrict_mem measurableSet_Icc
  have hb : ∀ᵐ z ∂coneRadialMeasure.prod (OAI.Analysis.Fourier.Restriction.sphereMeasure n), ‖coneData g z‖ ≤
      ‖((Real.sqrt 2 * 2 ^ (n - 1) : ℝ) : ℂ) * (g ∘ coneParam) z‖ := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hr] with z hz
    simpa [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg (2 : ℝ)), Function.comp_apply]
      using coneData_norm_bound g hz
  have hmem := (hu.const_mul ((Real.sqrt 2 * 2 ^ (n - 1) : ℝ) : ℂ)).mono hm hb
  refine ⟨hmem, ?_⟩
  calc
    _ ≤ eLpNorm (fun z => ((Real.sqrt 2 * 2 ^ (n - 1) : ℝ) : ℂ) *
        (g ∘ coneParam) z) p (coneRadialMeasure.prod (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) := eLpNorm_mono_ae hm hb
    _ = ENNReal.ofReal (Real.sqrt 2 * 2 ^ (n - 1)) *
        eLpNorm (g ∘ coneParam) p (coneRadialMeasure.prod (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) := by
      change eLpNorm (((Real.sqrt 2 * 2 ^ (n - 1) : ℝ) : ℂ) • (g ∘ coneParam)) p _ = _
      rw [eLpNorm_const_smul]
      simp only [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ Real.sqrt 2 * 2 ^ (n - 1) by positivity)]
    _ ≤ ENNReal.ofReal (Real.sqrt 2 * 2 ^ (n - 1)) *
        eLpNorm (g ∘ coneParam) p (coneParameterMeasure n) := by
      exact mul_le_mul' le_rfl (eLpNorm_mono_measure (g ∘ coneParam) (cone_unweighted_le n))
    _ = _ := by rw [← eLpNorm_map_measure hgm.aestronglyMeasurable hcp.aemeasurable]; rfl

end OAI.Analysis.Fourier.Cone
