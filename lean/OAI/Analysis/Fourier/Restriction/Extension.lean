import OAI.Analysis.Fourier.Restriction.Pairing
import OAI.Analysis.Fourier.Restriction.DualNorm

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- A global diagonal restriction estimate yields the dual diagonal
extension estimate for every sphere-`Lp` input, not only smooth inputs. -/
theorem sphericalExtension_bound_of_restriction {n : ℕ} {p : ℝ} (hp : 1 < p)
    {C : ℝ≥0∞} (hCt : C ≠ ⊤)
    (hrestriction : ∀ f : Space n → ℂ, Integrable f →
      MemLp f (ENNReal.ofReal (p / (p - 1))) volume →
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) (ENNReal.ofReal (p / (p - 1))) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        C * eLpNorm f (ENNReal.ofReal (p / (p - 1))) volume)
    {g : Space n → ℂ} (hg : MemLp g (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) :
    MemLp (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal p) volume ∧
      eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal p) volume ≤
        C * eLpNorm g (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
  have hgp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hp.le
  have hgi : Integrable g (OAI.Analysis.Fourier.Restriction.sphereMeasure n) :=
    memLp_one_iff_integrable.mp (hg.mono_exponent hgp)
  have hEg : AEStronglyMeasurable (OAI.Analysis.Fourier.Restriction.sphericalExtension g) volume :=
    (continuous_sphericalExtension hgi).aestronglyMeasurable
  have H : eLpNorm (OAI.Analysis.Fourier.Restriction.sphericalExtension g) (ENNReal.ofReal p) volume ≤
      C * eLpNorm g (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
    apply eLpNorm_le_of_integrable_pairing hp hEg (norm_sphericalExtension_le g)
    intro f hfi hfp
    have hfs : Integrable (fun x ↦ star (f x)) := by
      exact memLp_one_iff_integrable.mp (memLp_one_iff_integrable.mpr hfi).star
    have hfsp : MemLp (fun x ↦ star (f x)) (ENNReal.ofReal (p / (p - 1))) volume := hfp.star
    have hr := hrestriction (fun x ↦ star (f x)) hfs hfsp
    have hrm : MemLp (OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ star (f x)))
        (ENNReal.ofReal (p / (p - 1))) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) :=
      hr.trans_lt (ENNReal.mul_lt_top hCt.lt_top hfsp)
    rw [integral_sphericalExtension_pairing hfi hgi]
    have hpq : p.HolderConjugate (p / (p - 1)) :=
      (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl
    calc
      _ ≤ eLpNorm g (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) *
          eLpNorm (fun ω ↦ star (OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ star (f x)) ω))
            (ENNReal.ofReal (p / (p - 1))) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) :=
        OAI.Analysis.Fourier.BochnerRiesz.enorm_integral_mul_le_eLpNorm (OAI.Analysis.Fourier.Restriction.sphereMeasure n) hg.aestronglyMeasurable
          hrm.star.aestronglyMeasurable hpq
      _ = eLpNorm g (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) *
          eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ star (f x)))
            (ENNReal.ofReal (p / (p - 1))) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
        rw [show (fun ω ↦ star (OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ star (f x)) ω)) =
          star (OAI.Analysis.Fourier.LocalSmoothing.angularFourier (fun x ↦ star (f x))) from rfl, eLpNorm_star]
      _ ≤ eLpNorm g (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) *
          (C * eLpNorm (fun x ↦ star (f x)) (ENNReal.ofReal (p / (p - 1))) volume) := by
        exact mul_le_mul le_rfl hr zero_le zero_le
      _ = (C * eLpNorm g (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) *
          eLpNorm f (ENNReal.ofReal (p / (p - 1))) volume := by
        rw [show (fun x ↦ star (f x)) = star f from rfl, eLpNorm_star]
        simp only [mul_left_comm, mul_assoc]
  exact ⟨H.trans_lt (ENNReal.mul_lt_top hCt.lt_top hg), H⟩

end OAI.Analysis.Fourier.Restriction
