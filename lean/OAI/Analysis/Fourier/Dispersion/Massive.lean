import OAI.Analysis.Fourier.Dispersion.Low
import OAI.Analysis.Fourier.Dispersion.Product

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.Dispersion

theorem massive_weighted_bound_of_halfWave {n : ℕ} (m : ℝ) {p : ℝ} (hp : 1≤p)
    {w : Space n → ℝ} (hw : w.HasTemperateGrowth) (hw0 : ∀ ξ,w ξ≠0)
    (hbase : ∃ A : ℝ, 0<A ∧ ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal A * eLpNorm (OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier w f) (ENNReal.ofReal p) volume) :
    ∃ C : ℝ, 0<C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ ↦ massiveHalfWave m z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal C * eLpNorm (OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier w f) (ENNReal.ofReal p) volume := by
  by_cases hm : m=0
  · subst m
    simpa only [massiveHalfWave_zero] using hbase
  obtain ⟨A,hA,ha⟩ := hbase
  obtain ⟨L,hL,hl⟩ := lowHalfWave_weighted_bound hp hw hw0
  obtain ⟨D,hD,hd⟩ := massiveLow_weighted_bound m hm hp hw hw0
  obtain ⟨C,hC,hc⟩ := massiveCorrection_bound n m
  refine ⟨C*(A+L)+D,by positivity,fun f ↦ ?_⟩
  have hp1 : 1≤ENNReal.ofReal p := by
    simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  let u : Space n × ℝ → ℂ := fun z ↦ massiveHalfWave m z.2 f z.1 -
    massiveHalfWave m z.2 (velocityLowData f) z.1
  let v : Space n × ℝ → ℂ := fun z ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1 -
    OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 (velocityLowData f) z.1
  have hum : Measurable u := ((continuous_massiveHalfWave m f).sub
    (continuous_massiveHalfWave m (velocityLowData f))).measurable
  have hvm : Measurable v := ((OAI.Analysis.Fourier.LocalSmoothing.continuous_halfWaveIntegral f).sub
    (OAI.Analysis.Fourier.LocalSmoothing.continuous_halfWaveIntegral (velocityLowData f))).measurable
  have huv : eLpNorm u (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal C * eLpNorm v (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) := by
    apply eLpNorm_observation_le_mul_of_slices hum hvm (by linarith) hC.le
    intro t ht
    have he : (fun x ↦ u (x,t)) =
        complexAngularSchwartzMultiplier (massiveCorrection m t) (smoothHighWave t f) := by
      funext x
      exact (massiveCorrection_high_eq_sub m t f x).symm
    have hv : (fun x ↦ v (x,t)) = smoothHighWave t f := by
      funext x
      exact (smoothHighWave_eq_sub t f x).symm
    rw [he,hv]
    exact hc t ht (smoothHighWave t f) (ENNReal.ofReal p) hp1 ENNReal.ofReal_ne_top
  have hvb : eLpNorm v (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal (A+L) * eLpNorm (OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier w f) (ENNReal.ofReal p) volume := by
    exact (eLpNorm_sub_le hp1).trans ((add_le_add (ha f) (hl f)).trans_eq (by
      rw [← add_mul,← ENNReal.ofReal_add hA.le hL.le]))
  have he : (fun z : Space n × ℝ ↦ massiveHalfWave m z.2 f z.1) =
      fun z ↦ u z + massiveHalfWave m z.2 (velocityLowData f) z.1 := by
    funext z
    dsimp only [u]
    ring
  rw [he]
  calc
    _ ≤ eLpNorm u (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) +
        eLpNorm (fun z : Space n × ℝ ↦ massiveHalfWave m z.2 (velocityLowData f) z.1)
          (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) := eLpNorm_add_le hp1
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (A+L) *
          eLpNorm (OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier w f) (ENNReal.ofReal p) volume) +
        ENNReal.ofReal D * eLpNorm (OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier w f) (ENNReal.ofReal p) volume :=
      add_le_add (huv.trans (mul_le_mul' le_rfl hvb)) (hd f)
    _ = _ := by rw [← mul_assoc,← ENNReal.ofReal_mul hC.le,← add_mul,
      ← ENNReal.ofReal_add (mul_nonneg hC.le (add_nonneg hA.le hL.le)) hD.le]

theorem massive_logarithmicSobolev (hlog : OAI.Analysis.Fourier.LocalSmoothing.LogarithmicSobolev) {n : ℕ} (hn : 2≤n)
    (m : ℝ) {p B : ℝ} (hp : 2<p) (hB : 2*n+6<B) :
    ∃ C : ℝ, 0<C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ ↦ massiveHalfWave m z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal C * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p) B f)
        (ENNReal.ofReal p) volume := by
  let w : Space n → ℝ := fun ξ ↦ (1+‖ξ‖^2)^(OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p/2) *
    Real.log (2+Real.sqrt (1+‖ξ‖^2))^B
  have hw : w.HasTemperateGrowth := OAI.Analysis.Fourier.BesselPotential.temperate_log_bessel_weight _ _
  have hw0 (ξ : Space n) : w ξ≠0 := by
    apply mul_ne_zero
    · exact (Real.rpow_pos_of_pos (by positivity) _).ne'
    · apply (Real.rpow_pos_of_pos _ B).ne'
      exact Real.log_pos (by linarith [Real.sqrt_nonneg (1+‖ξ‖^2)])
  obtain ⟨A,hA,ha⟩ := hlog n hn p B hp hB
  have hb : ∃ A : ℝ, 0<A ∧ ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal A * eLpNorm (OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier w f) (ENNReal.ofReal p) volume := by
    refine ⟨A,hA,fun f ↦ ?_⟩
    change _ ≤ ENNReal.ofReal A * eLpNorm (OAI.Analysis.Fourier.BesselPotential.logBesselPotentialSchwartz (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p) B f) _ _
    simpa only [OAI.Analysis.Fourier.BesselPotential.logBesselPotentialSchwartz_eq] using (ha f).2.2
  obtain ⟨C,hC,hc⟩ := massive_weighted_bound_of_halfWave m (show 1≤p by linarith) hw hw0 hb
  refine ⟨C,hC,fun f ↦ ?_⟩
  have H := hc f
  change _ ≤ ENNReal.ofReal C * eLpNorm (OAI.Analysis.Fourier.BesselPotential.logBesselPotentialSchwartz (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p) B f) _ _ at H
  simpa only [OAI.Analysis.Fourier.BesselPotential.logBesselPotentialSchwartz_eq] using H

theorem massive_localSmoothing (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing) {n : ℕ} (hn : 2≤n)
    (m : ℝ) {p ε : ℝ} (hp : 2≤p) (hε : 0<ε ∨ (p=2 ∧ ε=0)) :
    ∃ C : ℝ, 0<C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ ↦ massiveHalfWave m z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal C * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.besselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p+ε) f)
        (ENNReal.ofReal p) volume := by
  let w : Space n → ℝ := fun ξ ↦ (1+‖ξ‖^2)^((OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p+ε)/2)
  have hw : w.HasTemperateGrowth := Function.hasTemperateGrowth_one_add_norm_sq_rpow _ _
  have hw0 (ξ : Space n) : w ξ≠0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
  obtain ⟨A,hA,ha⟩ := hls n hn p ε hp hε
  have hb : ∃ A : ℝ, 0<A ∧ ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal A * eLpNorm (OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier w f) (ENNReal.ofReal p) volume := by
    refine ⟨A,hA,fun f ↦ ?_⟩
    change _ ≤ ENNReal.ofReal A * eLpNorm (OAI.Analysis.Fourier.BesselPotential.besselPotentialSchwartz (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p+ε) f) _ _
    simpa only [OAI.Analysis.Fourier.BesselPotential.besselPotentialSchwartz_eq] using (ha f).2.2
  obtain ⟨C,hC,hc⟩ := massive_weighted_bound_of_halfWave m (show 1≤p by linarith) hw hw0 hb
  refine ⟨C,hC,fun f ↦ ?_⟩
  have H := hc f
  change _ ≤ ENNReal.ofReal C * eLpNorm (OAI.Analysis.Fourier.BesselPotential.besselPotentialSchwartz (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p+ε) f) _ _ at H
  simpa only [OAI.Analysis.Fourier.BesselPotential.besselPotentialSchwartz_eq] using H

end OAI.Analysis.Fourier.Dispersion
