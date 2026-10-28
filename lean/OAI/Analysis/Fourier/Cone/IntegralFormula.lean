import OAI.Analysis.Fourier.Cone.Slicing
import OAI.Analysis.Fourier.Cone.TimeFourier

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Cone

/-- Exact spherical slicing, including the induced surface-area weight. -/
theorem coneExtension_slicing {n : ℕ} {g : Space n × ℝ → ℂ}
    (hgm : Measurable g) (hg : Integrable g (coneMeasure n)) (x : Space n) (t : ℝ) :
    coneExtension g (x,t) = coneTimeFourier
      (fun ρ => OAI.Analysis.Fourier.Restriction.sphericalExtension (fun ω => coneData g (ρ,ω)) (ρ • x)) t := by
  let F : ℝ × Space n → ℂ := fun p => Complex.exp
    (Complex.I * ((inner ℝ x (p.1 • p.2) + t * p.1 : ℝ) : ℂ)) * coneData g p
  have hFi : Integrable F (coneRadialMeasure.prod (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) := by
    have hd := (coneData_lp_bound hgm (memLp_one_iff_integrable.mpr hg)).1
    have hdi := memLp_one_iff_integrable.mp hd
    apply hdi.norm.mono'
    · have hm : Measurable F := by
        have hgD := measurable_coneData hgm
        unfold F
        fun_prop
      exact hm.aestronglyMeasurable
    · filter_upwards [] with p
      simp [F, Complex.norm_exp]
  have hweight : Measurable (fun p : ℝ × Space n => ENNReal.ofReal (coneAreaWeight n p.1)) :=
    ((continuous_coneAreaWeight n).comp continuous_fst).measurable.ennreal_ofReal
  have hmap := integral_map (μ := coneParameterMeasure n)
    (continuous_coneParam n).measurable.aemeasurable (cone_integrand_integrable hg (x,t)).aestronglyMeasurable
  change coneExtension g (x,t) = _
  rw [coneExtension, coneMeasure, hmap, coneParameterMeasure,
    integral_withDensity_eq_integral_toReal_smul hweight
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have he : (fun p : ℝ × Space n =>
      (ENNReal.ofReal (coneAreaWeight n p.1)).toReal •
        (Complex.exp (Complex.I * ((inner ℝ (x,t).1 (coneParam p).1 +
          (x,t).2 * (coneParam p).2 : ℝ) : ℂ)) * g (coneParam p))) = F := by
    funext p
    rw [ENNReal.toReal_ofReal (coneAreaWeight_nonneg n p.1)]
    simp only [coneParam, F, coneData, Complex.real_smul]
    ring
  rw [he, integral_prod _ hFi]
  unfold coneTimeFourier
  apply integral_congr_ae
  filter_upwards [] with ρ
  rw [OAI.Analysis.Fourier.Restriction.sphericalExtension, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ω
  simp only [F, real_inner_smul_left, real_inner_smul_right]
  have hex : Complex.I * ((ρ * inner ℝ x ω + t * ρ : ℝ) : ℂ) =
      Complex.I * ((t * ρ : ℝ) : ℂ) + Complex.I * ((ρ * inner ℝ x ω : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hex, Complex.exp_add]
  ring

end OAI.Analysis.Fourier.Cone
