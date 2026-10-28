import OAI.Analysis.PDE.WaveEquation.VelocityBound
import OAI.Analysis.Fourier.LocalSmoothing.TimeReversal

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.PDE.WaveEquation

def highVelocityData {n : ℕ} (g : SchwartzMap (Space n) ℂ) : SchwartzMap (Space n) ℂ :=
  OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier velocityHighSymbol g

theorem highVelocityData_logBessel {n : ℕ} (s B : ℝ) (g : SchwartzMap (Space n) ℂ) :
    OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential s B (highVelocityData g) =
      OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier velocityShiftSymbol (OAI.Analysis.Fourier.BesselPotential.logBesselPotentialSchwartz (s-1) B g) := by
  funext x
  rw [OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier_eq_integral (temperate_velocityShiftSymbol n)]
  unfold OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential
  congr 1
  funext ξ
  rw [show OAI.Analysis.Fourier.LocalSmoothing.angularFourier (highVelocityData g) ξ =
      velocityHighSymbol ξ • OAI.Analysis.Fourier.LocalSmoothing.angularFourier g ξ from
    OAI.Analysis.Fourier.BesselPotential.angularFourier_angularSchwartzMultiplier (temperate_velocityHighSymbol n) g ξ]
  rw [show OAI.Analysis.Fourier.LocalSmoothing.angularFourier (OAI.Analysis.Fourier.BesselPotential.logBesselPotentialSchwartz (s-1) B g) ξ =
      ((1+‖ξ‖^2)^((s-1)/2) * Real.log (2+Real.sqrt (1+‖ξ‖^2))^B : ℝ) •
        OAI.Analysis.Fourier.LocalSmoothing.angularFourier g ξ by
    rw [OAI.Analysis.Fourier.BesselPotential.logBesselPotentialSchwartz_eq, OAI.Analysis.Fourier.BesselPotential.angularFourier_logBesselPotential]]
  have hp : (1+‖ξ‖^2)^((1:ℝ)/2) * (1+‖ξ‖^2)^((s-1)/2) =
      (1+‖ξ‖^2)^(s/2) := by
    rw [← Real.rpow_add (by positivity)]
    congr 1
    ring
  simp only [smul_smul, velocityShiftSymbol]
  congr 1
  calc
    _ = ((1+‖ξ‖^2)^((1:ℝ)/2) * (1+‖ξ‖^2)^((s-1)/2)) *
        velocityHighSymbol ξ * Real.log (2+Real.sqrt (1+‖ξ‖^2))^B := by rw [hp]; ring
    _ = _ := by ring

theorem highVelocityData_log_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s B : ℝ, ∀ g : SchwartzMap (Space n) ℂ,
      ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential s B (highVelocityData g)) p volume ≤
        ENNReal.ofReal C * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential (s-1) B g) p volume := by
  obtain ⟨C,hC,hb⟩ := velocityShiftSymbol_bound n
  refine ⟨C,hC,fun s B g p hp ht ↦ ?_⟩
  rw [highVelocityData_logBessel]
  simpa only [OAI.Analysis.Fourier.BesselPotential.logBesselPotentialSchwartz_eq] using hb (OAI.Analysis.Fourier.BesselPotential.logBesselPotentialSchwartz (s-1) B g) p hp ht

/-- The displacement part, with the two half-wave signs written explicitly. -/
def waveDisplacement {n : ℕ} (t : ℝ) (f : Space n → ℂ) (x : Space n) : ℂ :=
  (1/2 : ℝ) • (OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x + OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral (-t) f x)

/-- The high-frequency velocity part. -/
def waveHighVelocity {n : ℕ} (t : ℝ) (g : SchwartzMap (Space n) ℂ) (x : Space n) : ℂ :=
  Complex.I * ((1/2 : ℝ) • (OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t (highVelocityData g) x -
    OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral (-t) (highVelocityData g) x))

theorem logarithmicSobolev_displacement (hlog : OAI.Analysis.Fourier.LocalSmoothing.LogarithmicSobolev) {n : ℕ}
    (hn : 2 ≤ n) {p B : ℝ} (hp : 2 < p) (hB : 2*n+6 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ ↦ waveDisplacement z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal C * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p) B f)
        (ENNReal.ofReal p) volume := by
  obtain ⟨C,hC,hb⟩ := hlog n hn p B hp hB
  obtain ⟨D,hD,hd⟩ := OAI.Analysis.Fourier.LocalSmoothing.logarithmicSobolev_negative hlog hn hp hB
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

theorem logarithmicSobolev_highVelocity (hlog : OAI.Analysis.Fourier.LocalSmoothing.LogarithmicSobolev) {n : ℕ}
    (hn : 2 ≤ n) {p B : ℝ} (hp : 2 < p) (hB : 2*n+6 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ ↦ waveHighVelocity z.2 g z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal C * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p-1) B g)
        (ENNReal.ofReal p) volume := by
  obtain ⟨C,hC,hb⟩ := hlog n hn p B hp hB
  obtain ⟨D,hD,hd⟩ := OAI.Analysis.Fourier.LocalSmoothing.logarithmicSobolev_negative hlog hn hp hB
  obtain ⟨A,hA,ha⟩ := highVelocityData_log_bound n
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
    _ ≤ ENNReal.ofReal (C+D) * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p) B
        (highVelocityData g)) (ENNReal.ofReal p) volume :=
      (add_le_add (hb (highVelocityData g)).2.2 (hd (highVelocityData g)).2.2).trans_eq (by
        rw [← add_mul, ← ENNReal.ofReal_add hC.le hD.le])
    _ ≤ _ := (mul_le_mul' le_rfl (ha _ _ g _ hp1 ENNReal.ofReal_ne_top)).trans_eq (by
      rw [ENNReal.ofReal_mul (add_pos hC hD).le, mul_assoc])

end OAI.Analysis.PDE.WaveEquation
