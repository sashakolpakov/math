import OAI.Analysis.Fourier.Restriction.BumpDecay
import OAI.Analysis.Fourier.Restriction.GramKernel

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

def localizedFourierKernel {n : ℕ} (u : SchwartzMap (Space n) ℂ)
    (R : ℝ) (z ω ξ : Space n) : ℂ :=
  Complex.exp (-Complex.I * ((inner ℝ z ω : ℝ) : ℂ)) *
    OAI.Analysis.Fourier.LocalSmoothing.angularFourier (translatedFrequencyBump u R ξ) ω

theorem localizedFourierKernel_eq {n : ℕ} (u : SchwartzMap (Space n) ℂ)
    {R : ℝ} (hR : 0 < R) (z ω ξ : Space n) :
    localizedFourierKernel u R z ω ξ =
      Complex.exp (-Complex.I * ((inner ℝ z ω : ℝ) : ℂ)) *
        ((R ^ n : ℝ) : ℂ) * OAI.Analysis.Fourier.LocalSmoothing.angularFourier u (R • (ω - ξ)) := by
  rw [localizedFourierKernel, angularFourier_translatedFrequencyBump u hR]
  simp only [Complex.real_smul, mul_assoc]

theorem continuous_localizedFourierKernel {n : ℕ} (u : SchwartzMap (Space n) ℂ)
    {R : ℝ} (hR : 0 < R) (z : Space n) :
    Continuous (fun p : Space n × Space n ↦ localizedFourierKernel u R z p.1 p.2) := by
  simp_rw [localizedFourierKernel_eq u hR]
  have hF := continuous_angularFourier u.integrable
  fun_prop

theorem norm_localizedFourierKernel {n : ℕ} (u : SchwartzMap (Space n) ℂ)
    {R : ℝ} (hR : 0 < R) (z ω ξ : Space n) :
    ‖localizedFourierKernel u R z ω ξ‖ = R ^ n * ‖OAI.Analysis.Fourier.LocalSmoothing.angularFourier u (R • (ω - ξ))‖ := by
  rw [localizedFourierKernel_eq u hR]
  simp [Complex.norm_exp, abs_of_pos hR]

theorem star_fourier_translatedFrequencyBump {n : ℕ} (u : SchwartzMap (Space n) ℂ)
    (hu : ∀ ξ, star (OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ) = OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ)
    {R : ℝ} (hR : 0 < R) (ξ ω : Space n) :
    star (OAI.Analysis.Fourier.LocalSmoothing.angularFourier (translatedFrequencyBump u R ξ) ω) =
      OAI.Analysis.Fourier.LocalSmoothing.angularFourier (translatedFrequencyBump u R ξ) ω := by
  rw [angularFourier_translatedFrequencyBump u hR]
  simp only [star_smul, star_trivial, hu]

theorem localizedFourierKernel_gram {n : ℕ} (u : SchwartzMap (Space n) ℂ)
    (hu : ∀ ξ, star (OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ) = OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ)
    {R : ℝ} (hR : 0 < R) (z w ξ η : Space n) :
    (∫ ω, localizedFourierKernel u R z ω ξ *
      star (localizedFourierKernel u R w ω η) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) =
      OAI.Analysis.Fourier.Restriction.sphericalExtension (fun ω ↦ OAI.Analysis.Fourier.LocalSmoothing.angularFourier (translatedFrequencyBump u R ξ) ω *
        OAI.Analysis.Fourier.LocalSmoothing.angularFourier (translatedFrequencyBump u R η) ω) (w - z) := by
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [localizedFourierKernel, localizedFourierKernel, star_mul,
    star_fourier_translatedFrequencyBump u hu hR]
  have hstar : star (Complex.exp (-Complex.I * ((inner ℝ w ω : ℝ) : ℂ))) =
      Complex.exp (Complex.I * ((inner ℝ w ω : ℝ) : ℂ)) := by
    simp [← Complex.exp_conj]
  rw [hstar]
  change _ = Complex.exp (Complex.I * ((inner ℝ (w - z) ω : ℝ) : ℂ)) * _
  rw [inner_sub_left, Complex.ofReal_sub]
  have hexp : Complex.exp (-Complex.I * ((inner ℝ z ω : ℝ) : ℂ)) *
      Complex.exp (Complex.I * ((inner ℝ w ω : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (((inner ℝ w ω : ℝ) : ℂ) - ((inner ℝ z ω : ℝ) : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    _ = (Complex.exp (-Complex.I * ((inner ℝ z ω : ℝ) : ℂ)) *
      Complex.exp (Complex.I * ((inner ℝ w ω : ℝ) : ℂ))) *
      (OAI.Analysis.Fourier.LocalSmoothing.angularFourier (translatedFrequencyBump u R ξ) ω *
        OAI.Analysis.Fourier.LocalSmoothing.angularFourier (translatedFrequencyBump u R η) ω) := by ring
    _ = _ := by rw [hexp]

theorem localizedFourierKernel_gram_decay {n : ℕ} (hn : 1 ≤ n)
    (u : SchwartzMap (Space n) ℂ)
    (hu : ∀ ξ, star (OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ) = OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ z w ξ η : Space n,
      ‖∫ ω, localizedFourierKernel u R z ω ξ *
        star (localizedFourierKernel u R w ω η) ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n‖ ≤
      C * (R ^ n * R ^ (((n : ℝ) - 1) / 2)) ^ 2 *
        (1 + dist z w) ^ (-((n : ℝ) - 1) / 2) := by
  obtain ⟨C, hC, H⟩ := translatedFrequencyBump_product_decay hn u u
  refine ⟨C, hC, ?_⟩
  intro R hR z w ξ η
  rw [localizedFourierKernel_gram u hu (by linarith)]
  simpa only [dist_eq_norm, norm_sub_rev] using H R hR ξ η (w - z)

end OAI.Analysis.Fourier.Restriction
