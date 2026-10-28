import OAI.Analysis.Fourier.Cone.ProductNorm
import OAI.Analysis.Fourier.Cone.IntegralFormula
import OAI.Analysis.Fourier.Cone.InterpolationRange

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Cone

def coneTimeSynthesis {n : ℕ} (F : ℝ × Space n → ℂ) (z : Space n × ℝ) : ℂ :=
  coneTimeFourier (fun ρ => F (ρ,z.1)) z.2

theorem measurable_coneTimeSynthesis {n : ℕ} {F : ℝ × Space n → ℂ}
    (hF : Measurable F) : Measurable (coneTimeSynthesis F) := by
  have hm : StronglyMeasurable (fun z : (Space n × ℝ) × ℝ =>
      Complex.exp (Complex.I * ((z.1.2 * z.2 : ℝ) : ℂ)) * F (z.2,z.1.1)) := by
    apply Measurable.stronglyMeasurable
    have hFc : Measurable (fun z : (Space n × ℝ) × ℝ => F (z.2,z.1.1)) :=
      hF.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
    fun_prop
  exact (hm.integral_prod_right' (ν := coneRadialMeasure)).measurable

theorem coneTimeSynthesis_bound {n : ℕ} {F : ℝ × Space n → ℂ}
    (hF : Measurable F) {p : ℝ} (hp : 2 ≤ p)
    (hf : MemLp F (ENNReal.ofReal p) (coneRadialMeasure.prod volume)) :
    eLpNorm (coneTimeSynthesis F) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (2 * Real.pi) ^ (1 / p) *
        eLpNorm F (ENNReal.ofReal p) (coneRadialMeasure.prod volume) := by
  let Fs : Space n × ℝ → ℂ := fun z => F (z.2,z.1)
  have hFs : Measurable Fs := hF.comp measurable_swap
  have hnorm : eLpNorm Fs (ENNReal.ofReal p) (volume.prod coneRadialMeasure) =
      eLpNorm F (ENNReal.ofReal p) (coneRadialMeasure.prod volume) :=
    eLpNorm_comp_measurePreserving hF.aestronglyMeasurable Measure.measurePreserving_swap
  have hFsLp : MemLp Fs (ENNReal.ofReal p) (volume.prod coneRadialMeasure) := by
    rw [MemLp, hnorm]
    exact hf
  have hb : ∀ᵐ x ∂(volume : Measure (Space n)),
      eLpNorm (fun t => coneTimeSynthesis F (x,t)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (2 * Real.pi) ^ (1 / p) *
          eLpNorm (fun ρ => Fs (x,ρ)) (ENNReal.ofReal p) coneRadialMeasure := by
    filter_upwards [cone_ae_memLp_slice volume coneRadialMeasure hFs (by linarith) hFsLp]
      with x hx
    exact eLpNorm_coneTimeFourier hp hx
  have H := cone_product_norm_bound volume coneRadialMeasure volume hFs
    (measurable_coneTimeSynthesis hF) (by linarith : 0 < p) hb
  rw [hnorm] at H
  exact H

theorem cone_diagonal_of_sphere {n : ℕ} {p : ℝ} (hp : 2 ≤ p) {C : ℝ≥0∞}
    (hC : C ≠ ⊤)
    (hsphere : ∀ f : Space n → ℂ, MemLp f (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) →
      eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension f) (ENNReal.ofReal p) volume ≤
        C * eLpNorm f (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n))
    {g : Space n × ℝ → ℂ} (hgm : Measurable g) (hg : MemLp g (ENNReal.ofReal p) (coneMeasure n)) :
    eLpNorm (coneExtension g) (ENNReal.ofReal p) volume ≤
      (ENNReal.ofReal (2 * Real.pi) ^ (1 / p) * C *
        ENNReal.ofReal (Real.sqrt 2 * 2 ^ (n - 1))) * eLpNorm g (ENNReal.ofReal p) (coneMeasure n) := by
  have hgi := hg.integrable (show (1 : ℝ≥0∞) ≤ ENNReal.ofReal p by
    exact_mod_cast ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))
  have hd := coneData_lp_bound hgm hg
  have hdm := measurable_coneData hgm
  have hs := coneSpatialSlices_bound (show 1 ≤ p by linarith) hsphere hdm hd.1
  have hsm := measurable_coneSpatialSlices hdm
  have hsp : MemLp (coneSpatialSlices (coneData g)) (ENNReal.ofReal p)
      (coneRadialMeasure.prod volume) :=
    hs.trans_lt (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hC) hd.1)
  have ht := coneTimeSynthesis_bound hsm hp hsp
  have he : coneExtension g = coneTimeSynthesis (coneSpatialSlices (coneData g)) := by
    funext z
    exact coneExtension_slicing hgm hgi z.1 z.2
  rw [he]
  calc
    _ ≤ ENNReal.ofReal (2 * Real.pi) ^ (1 / p) *
        (C * eLpNorm (coneData g) (ENNReal.ofReal p) (coneRadialMeasure.prod (OAI.Analysis.Fourier.Restriction.sphereMeasure n))) :=
      ht.trans (mul_le_mul' le_rfl hs)
    _ ≤ ENNReal.ofReal (2 * Real.pi) ^ (1 / p) *
        (C * (ENNReal.ofReal (Real.sqrt 2 * 2 ^ (n - 1)) * eLpNorm g (ENNReal.ofReal p) (coneMeasure n))) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl hd.2)
    _ = _ := by ring

end OAI.Analysis.Fourier.Cone
