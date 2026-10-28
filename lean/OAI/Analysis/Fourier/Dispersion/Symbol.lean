import OAI.Analysis.Fourier.Dispersion.Multiplier
import OAI.Analysis.Fourier.WavePackets.Half.Wave.LowFamily

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology
noncomputable section
namespace OAI.Analysis.Fourier.Dispersion

def regularizedRadius {n : ℕ} (ξ : Space n) : ℝ := Real.sqrt (OAI.Analysis.PDE.WaveEquation.velocityRadiusSq ξ)

def massiveCorrection {n : ℕ} (m t : ℝ) (ξ : Space n) : ℂ :=
  Complex.exp (-Complex.I * (t *
    (Real.sqrt (m^2 + OAI.Analysis.PDE.WaveEquation.velocityRadiusSq ξ) - regularizedRadius ξ) : ℝ))

theorem temperate_regularizedRadius (n : ℕ) :
    (@regularizedRadius n).HasTemperateGrowth := by
  change (fun ξ : Space n ↦ Real.sqrt (OAI.Analysis.PDE.WaveEquation.velocityRadiusSq ξ)).HasTemperateGrowth
  simpa only [Real.sqrt_eq_rpow] using
    OAI.Analysis.Fourier.BesselPotential.temperate_rpow_of_half_lt (OAI.Analysis.PDE.WaveEquation.temperate_velocityRadiusSq n)
      (fun ξ ↦ lt_of_lt_of_le (by norm_num) (OAI.Analysis.PDE.WaveEquation.velocityRadiusSq_one_le ξ)) (1/2)

theorem temperate_massiveCorrection (n : ℕ) (m t : ℝ) :
    (massiveCorrection (n := n) m t).HasTemperateGrowth := by
  have hs : (fun ξ : Space n ↦ Real.sqrt (m^2+OAI.Analysis.PDE.WaveEquation.velocityRadiusSq ξ)).HasTemperateGrowth := by
    have hb : (fun ξ : Space n ↦ m^2+OAI.Analysis.PDE.WaveEquation.velocityRadiusSq ξ).HasTemperateGrowth :=
      (Function.HasTemperateGrowth.const (m^2)).add (OAI.Analysis.PDE.WaveEquation.temperate_velocityRadiusSq n)
    simpa only [Real.sqrt_eq_rpow] using
      OAI.Analysis.Fourier.BesselPotential.temperate_rpow_of_half_lt hb
        (fun ξ ↦ by have h := OAI.Analysis.PDE.WaveEquation.velocityRadiusSq_one_le ξ; nlinarith [sq_nonneg m]) (1/2)
  have h := Complex.hasTemperateGrowth_exp_mul_I.comp
    (((Function.HasTemperateGrowth.const (-t)).mul
      (hs.sub (temperate_regularizedRadius n))))
  have he : massiveCorrection (n := n) m t = fun ξ ↦
      Complex.exp ((-t*(Real.sqrt (m^2+OAI.Analysis.PDE.WaveEquation.velocityRadiusSq ξ)-regularizedRadius ξ):ℝ)*Complex.I) := by
    funext ξ
    unfold massiveCorrection
    congr 1
    push_cast
    ring
  rw [he]
  exact h

theorem contDiff_massiveCorrection (n : ℕ) (m : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × Space n ↦ massiveCorrection m z.1 z.2) := by
  have hR : ContDiff ℝ ∞ (fun z : ℝ × Space n ↦ OAI.Analysis.PDE.WaveEquation.velocityRadiusSq z.2) :=
    (OAI.Analysis.PDE.WaveEquation.temperate_velocityRadiusSq n).1.comp contDiff_snd
  have hR0 (z : ℝ × Space n) : OAI.Analysis.PDE.WaveEquation.velocityRadiusSq z.2 ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (OAI.Analysis.PDE.WaveEquation.velocityRadiusSq_one_le z.2))
  have hm0 (z : ℝ × Space n) : m^2+OAI.Analysis.PDE.WaveEquation.velocityRadiusSq z.2 ≠ 0 := by
    have h := OAI.Analysis.PDE.WaveEquation.velocityRadiusSq_one_le z.2
    nlinarith [sq_nonneg m]
  exact Complex.contDiff_exp.comp (contDiff_const.mul
    (Complex.ofRealCLM.contDiff.comp
      (contDiff_fst.mul (((contDiff_const.add hR).sqrt hm0).sub (hR.sqrt hR0)))))

def massiveAnnularDifference {n : ℕ} (m h : ℝ) (ξ : Space n) : ℝ :=
  m^2 / (Real.sqrt ((m*h)^2+‖ξ‖^2)+‖ξ‖)

def massiveCorrectionAnnulus {n : ℕ} (m : ℝ) (z : (ℝ × ℝ) × Space n) : ℂ :=
  OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff z.2 *
    (-Complex.I * (z.1.1 * massiveAnnularDifference m z.1.2 z.2 : ℝ)) *
    dslope Complex.exp 0
      (-Complex.I * (z.1.1*z.1.2*massiveAnnularDifference m z.1.2 z.2 : ℝ))

theorem massiveCorrectionAnnulus_identity {n : ℕ} (m t h : ℝ) (ξ : Space n) :
    (h:ℂ) * massiveCorrectionAnnulus m ((t,h),ξ) =
      OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff ξ *
        (Complex.exp (-Complex.I * (t*h*massiveAnnularDifference m h ξ:ℝ))-1) := by
  have H := sub_smul_dslope Complex.exp (0:ℂ)
    (-Complex.I * (t*h*massiveAnnularDifference m h ξ:ℝ))
  simp only [sub_zero,smul_eq_mul,Complex.exp_zero] at H
  unfold massiveCorrectionAnnulus
  rw [← H]
  push_cast
  ring

theorem contDiff_massiveCorrectionAnnulus (n : ℕ) (m : ℝ) :
    ContDiff ℝ ∞ (massiveCorrectionAnnulus (n := n) m) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z.2 ∈ tsupport (@OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff n)
  · have hx : z.2 ≠ 0 := by
      intro he; exact OAI.Analysis.Fourier.LocalSmoothing.zero_notMem_tsupport_smoothingAnnularCutoff n (he ▸ hz)
    have hn := (contDiffAt_snd : ContDiffAt ℝ ∞
      (fun z : (ℝ×ℝ)×Space n ↦ z.2) z).norm ℝ hx
    have hs : ContDiffAt ℝ ∞ (fun z : (ℝ×ℝ)×Space n ↦
        Real.sqrt ((m*z.1.2)^2+‖z.2‖^2)) z :=
      (((contDiffAt_const.mul contDiffAt_fst.snd).pow 2).add
        (ContDiffAt.norm_sq (𝕜 := ℝ) contDiffAt_snd)).sqrt (by positivity)
    have hd : ContDiffAt ℝ ∞ (fun z : (ℝ×ℝ)×Space n ↦
        massiveAnnularDifference m z.1.2 z.2) z :=
      contDiffAt_const.div (hs.add hn) (by positivity)
    have hL := (contDiffAt_const (c := -Complex.I)).mul (Complex.ofRealCLM.contDiff.contDiffAt.comp z
      (contDiffAt_fst.fst.mul hd))
    have hS := (contDiffAt_const (c := -Complex.I)).mul (Complex.ofRealCLM.contDiff.contDiffAt.comp z
      ((contDiffAt_fst.fst.mul contDiffAt_fst.snd).mul hd))
    exact (((OAI.Analysis.Fourier.LocalSmoothing.contDiff_smoothingAnnularCutoff n).contDiffAt.comp z contDiffAt_snd).mul hL).mul
      (OAI.Analysis.Fourier.WavePackets.contDiff_exp_dslope.contDiffAt.comp z hS)
  · have he := (notMem_tsupport_iff_eventuallyEq.mp hz).comp_tendsto
      (continuous_snd.tendsto z)
    apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    simp only [massiveCorrectionAnnulus,show OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff y.2 = 0 from hy,zero_mul]

theorem tsupport_massiveCorrectionAnnulus (n : ℕ) (m : ℝ) :
    tsupport (massiveCorrectionAnnulus (n := n) m) ⊆
      univ ×ˢ tsupport (@OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff n) := by
  intro z hz
  refine ⟨trivial,tsupport_comp_subset_preimage _ continuous_snd ?_⟩
  exact tsupport_mul_subset_left (tsupport_mul_subset_left hz)

end OAI.Analysis.Fourier.Dispersion
