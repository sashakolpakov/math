import OAI.Analysis.Fourier.SquareFunction.Maximal.BRNorm

open OAI.Analysis.Fourier.Wave

/-! The maximal Bochner--Riesz implication, for the actual supremum over all
positive radii. Smooth factors are controlled pointwise by Hardy--Littlewood,
before the strict-index shell series is summed. -/

open _root_.MeasureTheory
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.SquareFunction


theorem localSmoothing_maximalBochnerRiesz (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {p δ : ℝ} (hp : 2 ≤ p) (hδ : OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszMaximal δ f) (ENNReal.ofReal p) volume ∧
      eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszMaximal δ f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume := by
  have hδ0 : 0 < δ := lt_of_le_of_lt (le_max_left _ _) hδ
  have hp' : 1 < p := by linarith
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp'.le
  let ε : ℝ := (δ - OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hgap : OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε < δ := by dsimp [ε]; linarith
  obtain ⟨χ, hχ, hc, hzero, hone, _⟩ := OAI.Analysis.Fourier.BochnerRiesz.exists_annular_cutoff (n := n)
    (a := 1 / 4) (b := 1 / 2) (c := 2) (d := 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨C₀, hC₀, L, _, hmax⟩ := OAI.Analysis.Fourier.BochnerRiesz.localSmoothing_maximalShellCycles hls hn
    (OAI.Analysis.Fourier.BochnerRiesz.dyadicPowerProfile δ) (OAI.Analysis.Fourier.BochnerRiesz.hasCompactSupport_dyadicPowerProfile δ) hp hε
  obtain ⟨J₀, hJ₀⟩ := pow_unbounded_of_one_lt L (by norm_num : (1 : ℝ) < 2)
  let J : ℕ := J₀ + 2
  have hJ : 2 ≤ J := by dsimp [J]; omega
  have hlarge (j : ℕ) : L ≤ (2 : ℝ) ^ (J + j) :=
    hJ₀.le.trans (pow_le_pow_right₀ (by norm_num) (by dsimp [J]; omega))
  obtain ⟨K, hK, hpacket⟩ := brScaledPacket_maximal_bound (δ := δ) hχ hc hzero
  obtain ⟨B, hB, hinterior⟩ := brScaledInterior_maximal_bound (n := n) hδ0 hJ
  obtain ⟨D, hD, hHL⟩ := exists_ballMaximal_envelope_constant n hp'
  let G : ℝ := (1 - (2 : ℝ) ^ ((OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p + ε) - δ))⁻¹
  have hG : 0 < G := OAI.Analysis.Fourier.BochnerRiesz.dyadic_rpow_sum_constant_pos hgap
  let C : ℝ := B * D + (K * D * C₀) * G
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro f
  have hi := eLpNorm_brMaximalInteriorEnvelope_le hp' hB.le hHL f
  have hs := eLpNorm_brMaximalShellEnvelope_le hp' hK.le hC₀.le hD.le hgap J hHL f
    (fun j => (hmax _ (hlarge j) f).2)
  have H : eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszMaximal δ f) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume := by
    calc
      _ ≤ eLpNorm (fun x => ENNReal.ofReal B * ballMaximal volume (fun y => ‖f y‖ₑ) x +
          brMaximalShellEnvelope δ K J f x) (ENNReal.ofReal p) volume := by
        apply eLpNorm_mono_enorm (measurable_bochnerRieszMaximal hδ0.le f).aestronglyMeasurable
        intro x
        simp only [enorm_eq_self]
        exact bochnerRieszMaximal_le_shell_envelope hδ0 hJ hχ hc hzero hone hinterior hpacket f x
      _ ≤ eLpNorm (fun x => ENNReal.ofReal B * ballMaximal volume (fun y => ‖f y‖ₑ) x)
          (ENNReal.ofReal p) volume + eLpNorm (brMaximalShellEnvelope δ K J f)
          (ENNReal.ofReal p) volume := eLpNorm_add_le hp1
      _ ≤ ENNReal.ofReal (B * D) * eLpNorm f (ENNReal.ofReal p) volume +
          ENNReal.ofReal ((K * D * C₀) * G) * eLpNorm f (ENNReal.ofReal p) volume :=
        add_le_add hi hs
      _ = _ := by
        rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ⟨H.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (f.memLp _ volume).eLpNorm_lt_top), H⟩

theorem localSmoothing_maximalBochnerRieszConjecture (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing) :
    OAI.Analysis.Fourier.BochnerRiesz.MaximalBochnerRieszConjecture := by
  intro n hn p δ hp hδ
  exact localSmoothing_maximalBochnerRiesz hls hn hp hδ

end OAI.Analysis.Fourier.SquareFunction
