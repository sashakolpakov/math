import OAI.Analysis.Fourier.Restriction.ShiftedAnnulus
import OAI.Analysis.Fourier.Restriction.NormPair
import OAI.MeasureTheory.Kakeya.Maximal

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem annular_norm_pair_bound {n : ℕ} (hn : 1 ≤ n)
    {G U : Space n → ℂ} (hG : Measurable G) (hU : Measurable U)
    {p c W E a b d : ℝ} (hp : 1 ≤ p) (hc : 0 ≤ c) (hW : 0 ≤ W) (hE : 0 ≤ E)
    (ha : 0 < a) (hd : 0 ≤ d)
    (hbound : ∀ ω : Space n, ‖ω‖ = 1 → ∀ t ∈ Icc a b,
      c * ‖G ω‖ ≤ W * (‖U (t • ω)‖ + ‖U ((t + d) • ω)‖) + E) :
    ENNReal.ofReal c * (eLpNorm G (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) *
      ENNReal.ofReal (b - a) ^ (1 / p)) ≤
    ENNReal.ofReal W * (2 * (((ENNReal.ofReal (a ^ (n - 1)))⁻¹) ^ (1 / p) *
      eLpNorm U (ENNReal.ofReal p) volume)) +
    ENNReal.ofReal E * (OAI.Analysis.Fourier.Restriction.sphereMeasure n univ * ENNReal.ofReal (b - a)) ^ (1 / p) := by
  let μ := (OAI.Analysis.Fourier.Restriction.sphereMeasure n).prod (volume.restrict (Icc a b))
  let F : Space n × ℝ → ℂ := fun z ↦ (c : ℂ) * G z.1
  let V : Space n × ℝ → ℂ := fun z ↦ U (z.2 • z.1)
  let Z : Space n × ℝ → ℂ := fun z ↦ U ((z.2 + d) • z.1)
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hV : Measurable V := by dsimp [V]; fun_prop
  have hZ : Measurable Z := by dsimp [Z]; fun_prop
  have ho : ∀ᵐ z : Space n × ℝ ∂μ, ‖z.1‖ = 1 := by
    apply (Measure.ae_prod_iff_ae_ae
      ((isClosed_eq (continuous_norm.comp continuous_fst) continuous_const).measurableSet :
        MeasurableSet {z : Space n × ℝ | ‖z.1‖ = 1})).mpr
    filter_upwards [OAI.MeasureTheory.Kakeya.ae_sphereMeasure_norm n] with ω hω
    exact Filter.Eventually.of_forall fun _ ↦ hω
  have ht : ∀ᵐ z : Space n × ℝ ∂μ, z.2 ∈ Icc a b := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.preimage measurable_snd)).mpr
    exact Filter.Eventually.of_forall fun _ ↦ ae_restrict_mem measurableSet_Icc
  have hpoint : ∀ᵐ z ∂μ, ‖F z‖ ≤ W * (‖V z‖ + ‖Z z‖) + E := by
    filter_upwards [ho, ht] with z hz ht
    simpa only [F, V, Z, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
      using hbound z.1 hz z.2 ht
  have H := eLpNorm_le_norm_pair μ hF.aestronglyMeasurable hV.aestronglyMeasurable
    hZ.aestronglyMeasurable hp hW hE hpoint
  have hnorm : eLpNorm F (ENNReal.ofReal p) μ =
      ENNReal.ofReal c * (eLpNorm G (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) *
        ENNReal.ofReal (b - a) ^ (1 / p)) := by
    change eLpNorm ((c : ℂ) • (fun z : Space n × ℝ ↦ G z.1)) _ _ = _
    have hc' : ‖(c : ℂ)‖ₑ = ENNReal.ofReal c := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
    rw [eLpNorm_const_smul, hc']
    rw [eLpNorm_fun_fst (OAI.Analysis.Fourier.Restriction.sphereMeasure n) (volume.restrict (Icc a b)) hG (by linarith)]
    simp only [Measure.restrict_apply_univ, Real.volume_Icc]
  rw [hnorm] at H
  have hVb := eLpNorm_radial_annulus_le hn hU (by linarith : 0 < p) ha b
  have hZb := eLpNorm_shifted_radial_annulus_le hn hU (by linarith : 0 < p) ha b hd
  have hmass : μ univ = OAI.Analysis.Fourier.Restriction.sphereMeasure n univ * ENNReal.ofReal (b - a) := by
    dsimp [μ]
    rw [← Set.univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ, Real.volume_Icc]
  rw [hmass] at H
  apply H.trans
  gcongr
  simpa only [two_mul] using add_le_add hVb hZb

end OAI.Analysis.Fourier.Restriction
