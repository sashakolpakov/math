import OAI.Analysis.Fourier.Cone.Geometry
import OAI.Analysis.Fourier.Restriction.Basic

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal

noncomputable section
namespace OAI.Analysis.Fourier.Cone

def coneRadialMeasure : Measure ℝ := volume.restrict (Icc 1 2)

instance : IsFiniteMeasure coneRadialMeasure := by
  unfold coneRadialMeasure
  infer_instance

@[simp] theorem coneRadialMeasure_univ : coneRadialMeasure univ = 1 := by
  norm_num [coneRadialMeasure]

def coneAreaWeight (n : ℕ) (ρ : ℝ) : ℝ := Real.sqrt 2 * (max ρ 0) ^ (n - 1)

theorem continuous_coneAreaWeight (n : ℕ) : Continuous (coneAreaWeight n) := by
  unfold coneAreaWeight
  fun_prop

theorem coneAreaWeight_nonneg (n : ℕ) (ρ : ℝ) : 0 ≤ coneAreaWeight n ρ := by
  unfold coneAreaWeight
  positivity

theorem coneAreaWeight_eq {n : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) :
    coneAreaWeight n ρ = Real.sqrt 2 * ρ ^ (n - 1) := by
  simp [coneAreaWeight, max_eq_left hρ]

theorem coneAreaWeight_bounds (n : ℕ) {ρ : ℝ} (hρ : ρ ∈ Icc (1 : ℝ) 2) :
    1 ≤ coneAreaWeight n ρ ∧ coneAreaWeight n ρ ≤ Real.sqrt 2 * 2 ^ (n - 1) := by
  rw [coneAreaWeight_eq (by linarith [hρ.1])]
  have hs : 1 ≤ Real.sqrt (2 : ℝ) := by
    exact (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  constructor
  · have hp : 1 ≤ ρ ^ (n - 1) := one_le_pow₀ hρ.1
    nlinarith
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [hρ.1]) hρ.2 _)
      (Real.sqrt_nonneg _)

/-- Surface measure in the standard cone chart. The weight is the square
root of the induced tangent Gram determinant, computed in `ConeGeometry`. -/
def coneParameterMeasure (n : ℕ) : Measure (ℝ × Space n) :=
  (coneRadialMeasure.prod (OAI.Analysis.Fourier.Restriction.sphereMeasure n)).withDensity
    (fun p => ENNReal.ofReal (coneAreaWeight n p.1))

instance coneParameterMeasure_finite (n : ℕ) : IsFiniteMeasure (coneParameterMeasure n) := by
  apply isFiniteMeasure_withDensity
  apply ne_of_lt
  apply lt_of_le_of_lt (lintegral_mono_ae ?_)
    (show (∫⁻ _ : ℝ × Space n, ENNReal.ofReal (Real.sqrt 2 * 2 ^ (n - 1))
      ∂coneRadialMeasure.prod (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) < ⊤ by
        simp only [lintegral_const]
        finiteness)
  have hr : ∀ᵐ ρ ∂coneRadialMeasure, ρ ∈ Icc (1 : ℝ) 2 :=
    ae_restrict_mem measurableSet_Icc
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hr] with p hp
  exact ENNReal.ofReal_le_ofReal (coneAreaWeight_bounds n hp).2

/-- The induced surface measure on the truncated forward cone, represented
as an ambient measure. -/
def coneMeasure (n : ℕ) : Measure (Space n × ℝ) :=
  (coneParameterMeasure n).map coneParam

instance coneMeasure_finite (n : ℕ) : IsFiniteMeasure (coneMeasure n) := by
  unfold coneMeasure
  infer_instance

theorem continuous_coneParam (n : ℕ) : Continuous (@coneParam n) := by
  unfold coneParam
  fun_prop

def coneExtension {n : ℕ} (g : Space n × ℝ → ℂ) (z : Space n × ℝ) : ℂ :=
  ∫ η, Complex.exp (Complex.I * ((inner ℝ z.1 η.1 + z.2 * η.2 : ℝ) : ℂ)) * g η
    ∂coneMeasure n

theorem cone_character_norm {n : ℕ} (z η : Space n × ℝ) :
    ‖Complex.exp (Complex.I * ((inner ℝ z.1 η.1 + z.2 * η.2 : ℝ) : ℂ))‖ = 1 := by
  simp [Complex.norm_exp]

theorem cone_integrand_integrable {n : ℕ} {g : Space n × ℝ → ℂ}
    (hg : Integrable g (coneMeasure n)) (z : Space n × ℝ) :
    Integrable (fun η => Complex.exp
      (Complex.I * ((inner ℝ z.1 η.1 + z.2 * η.2 : ℝ) : ℂ)) * g η) (coneMeasure n) := by
  apply hg.norm.mono'
  · have hc : Continuous (fun η : Space n × ℝ => Complex.exp
        (Complex.I * ((inner ℝ z.1 η.1 + z.2 * η.2 : ℝ) : ℂ))) := by fun_prop
    exact hc.aestronglyMeasurable.mul hg.aestronglyMeasurable
  · exact Eventually.of_forall fun η => by simp only [norm_mul, cone_character_norm, one_mul, le_refl]

theorem continuous_coneExtension {n : ℕ} {g : Space n × ℝ → ℂ}
    (hg : Integrable g (coneMeasure n)) : Continuous (coneExtension g) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply tendsto_integral_filter_of_dominated_convergence (fun η => ‖g η‖)
  · exact Eventually.of_forall fun y => (cone_integrand_integrable hg y).aestronglyMeasurable
  · exact Eventually.of_forall fun y => Eventually.of_forall fun η => by
      simp only [norm_mul, cone_character_norm, one_mul, le_refl]
  · exact hg.norm
  · exact Eventually.of_forall fun η => Continuous.tendsto (by fun_prop) z

theorem enorm_coneExtension_le {n : ℕ} (g : Space n × ℝ → ℂ) (z : Space n × ℝ) :
    ‖coneExtension g z‖ₑ ≤ ∫⁻ η, ‖g η‖ₑ ∂coneMeasure n := by
  apply (enorm_integral_le_lintegral_enorm _).trans_eq
  apply lintegral_congr
  intro η
  simp only [← ofReal_norm, norm_mul, cone_character_norm, one_mul]

end OAI.Analysis.Fourier.Cone
