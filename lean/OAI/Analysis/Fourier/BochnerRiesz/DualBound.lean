import OAI.Analysis.Fourier.BochnerRiesz.SchwartzDuality
import OAI.Analysis.Fourier.BochnerRiesz.Pairing
import OAI.Analysis.Fourier.BochnerRiesz.PacketNorm

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem brInteriorCycles_dual_bound {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {J : ℕ} (hJ : 2 ≤ J) {p : ℝ} (hp : 1 < p) {C : ℝ}
    (hbound : ∀ g : SchwartzMap (Space n) ℂ,
      eLpNorm (brInteriorCycles δ J g) (ENNReal.ofReal (p / (p - 1))) volume ≤
        ENNReal.ofReal C * eLpNorm g (ENNReal.ofReal (p / (p - 1))) volume)
    (f : SchwartzMap (Space n) ℂ) :
    eLpNorm (brInteriorCycles δ J f) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume := by
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le
  obtain ⟨K, hK, hkernel⟩ := exists_angularInverse_kernel_bound
    (contDiff_brInteriorSymbol hδ hJ) (hasCompactSupport_brInteriorSymbol hδ J)
  have hfp : MemLp (brInteriorCycles δ J f) (ENNReal.ofReal p) volume := by
    have H := (eLpNorm_brInteriorCycles_le hδ hJ f hp1 ENNReal.ofReal_ne_top).trans
      (mul_le_mul' hkernel le_rfl)
    exact H.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (f.memLp _ volume).eLpNorm_lt_top)
  apply eLpNorm_le_of_schwartz_pairing hp hfp
  intro g
  rw [brInteriorCycles_integral_pairing hδ hJ f g]
  have hpq : p.HolderConjugate (p / (p - 1)) := (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl
  calc
    _ ≤ eLpNorm f (ENNReal.ofReal p) volume *
        eLpNorm (brInteriorCycles δ J g) (ENNReal.ofReal (p / (p - 1))) volume :=
      enorm_integral_mul_le_eLpNorm volume f.continuous.aestronglyMeasurable
        (continuous_brInteriorCycles hδ hJ g).aestronglyMeasurable hpq
    _ ≤ eLpNorm f (ENNReal.ofReal p) volume *
        (ENNReal.ofReal C * eLpNorm g (ENNReal.ofReal (p / (p - 1))) volume) :=
      mul_le_mul' le_rfl (hbound g)
    _ = _ := by ring

end OAI.Analysis.Fourier.BochnerRiesz
