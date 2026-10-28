import OAI.Analysis.PDE.WaveEquation.Membership

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.PDE.WaveEquation

theorem logBesselPotential_zero_log {n : ℕ} (s : ℝ) (f : SchwartzMap (Space n) ℂ) :
    OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential s 0 f = OAI.Analysis.Fourier.LocalSmoothing.besselPotential s f := by
  simp only [OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential,OAI.Analysis.Fourier.LocalSmoothing.besselPotential,Real.rpow_zero,mul_one]

theorem highVelocityData_bessel_bound (n : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ s : ℝ,∀ g : SchwartzMap (Space n) ℂ,
      ∀ p : ℝ≥0∞,1≤p → p≠⊤ →
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.besselPotential s (highVelocityData g)) p volume ≤
        ENNReal.ofReal C * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.besselPotential (s-1) g) p volume := by
  obtain ⟨C,hC,hb⟩ := highVelocityData_log_bound n
  exact ⟨C,hC,fun s g p hp ht ↦ by
    simpa only [logBesselPotential_zero_log] using hb s 0 g p hp ht⟩

theorem localSmoothing_waveDisplacement (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing) {n : ℕ}
    (hn : 2 ≤ n) {p ε : ℝ} (hp : 2 ≤ p) (hε : 0<ε ∨ (p=2 ∧ ε=0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ ↦ waveDisplacement z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal C * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.besselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p+ε) f)
        (ENNReal.ofReal p) volume := by
  obtain ⟨C,hC,hb⟩ := hls n hn p ε hp hε
  obtain ⟨D,hD,hd⟩ := OAI.Analysis.Fourier.LocalSmoothing.euclideanLocalSmoothing_negative hls hn hp hε
  refine ⟨C+D,add_pos hC hD,fun f ↦ ?_⟩
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show (1:ℝ)≤p by linarith)
  change eLpNorm ((1/2:ℝ) • (fun z : Space n × ℝ ↦
    OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1 + OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral (-z.2) f z.1)) _ _ ≤ _
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (by norm_num : (0:ℝ)≤1/2)]
  calc
    _ ≤ eLpNorm (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1 +
        OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral (-z.2) f z.1) (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) :=
      (mul_le_mul' (by norm_num : ENNReal.ofReal (1/2:ℝ) ≤ 1) le_rfl).trans_eq (one_mul _)
    _ ≤ _ + _ := eLpNorm_add_le hp1
    _ ≤ _ := (add_le_add (hb f).2.2 (hd f).2.2).trans_eq (by
      rw [← add_mul, ← ENNReal.ofReal_add hC.le hD.le])

theorem localSmoothing_waveHighVelocity (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing) {n : ℕ}
    (hn : 2 ≤ n) {p ε : ℝ} (hp : 2 ≤ p) (hε : 0<ε ∨ (p=2 ∧ ε=0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ ↦ waveHighVelocity z.2 g z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal C * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.besselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p+ε-1) g)
        (ENNReal.ofReal p) volume := by
  obtain ⟨C,hC,hb⟩ := hls n hn p ε hp hε
  obtain ⟨D,hD,hd⟩ := OAI.Analysis.Fourier.LocalSmoothing.euclideanLocalSmoothing_negative hls hn hp hε
  obtain ⟨A,hA,ha⟩ := highVelocityData_bessel_bound n
  refine ⟨(C+D)*A,mul_pos (add_pos hC hD) hA,fun g ↦ ?_⟩
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show (1:ℝ)≤p by linarith)
  change eLpNorm (Complex.I • ((1/2:ℝ) • (fun z : Space n × ℝ ↦
    OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 (highVelocityData g) z.1 -
      OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral (-z.2) (highVelocityData g) z.1))) _ _ ≤ _
  rw [eLpNorm_const_smul, eLpNorm_const_smul, enorm_eq_nnnorm, Complex.nnnorm_I,
    ENNReal.coe_one, one_mul, Real.enorm_eq_ofReal (by norm_num : (0:ℝ)≤1/2)]
  calc
    _ ≤ eLpNorm (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 (highVelocityData g) z.1 -
        OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral (-z.2) (highVelocityData g) z.1) (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) :=
      (mul_le_mul' (by norm_num : ENNReal.ofReal (1/2:ℝ) ≤ 1) le_rfl).trans_eq (one_mul _)
    _ ≤ _ + _ := eLpNorm_sub_le hp1
    _ ≤ ENNReal.ofReal (C+D) * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.besselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p+ε)
        (highVelocityData g)) (ENNReal.ofReal p) volume :=
      (add_le_add (hb (highVelocityData g)).2.2 (hd (highVelocityData g)).2.2).trans_eq (by
        rw [← add_mul, ← ENNReal.ofReal_add hC.le hD.le])
    _ ≤ _ := (mul_le_mul' le_rfl (ha _ g _ hp1 ENNReal.ofReal_ne_top)).trans_eq (by
      rw [ENNReal.ofReal_mul (add_pos hC hD).le, mul_assoc])

end OAI.Analysis.PDE.WaveEquation
