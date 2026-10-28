import OAI.Analysis.Fourier.BochnerRiesz.TimeReversal

open OAI.Analysis.Fourier.Wave

/-! The two signs of the propagator, as stated after `cor:log-sobolev`. -/

open _root_.MeasureTheory
open scoped ENNReal ComplexConjugate ContDiff Topology
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing

theorem angular_real_even_multiplier_conj {n : ℕ}
    (m : Space n → ℝ) (hm : ∀ ξ, m (-ξ) = m ξ) (f : Space n → ℂ) (x : Space n) :
    angularInverse (fun ξ => m ξ • angularFourier (fun y => conj (f y)) ξ) x =
      conj (angularInverse (fun ξ => m ξ • angularFourier f ξ) x) := by
  let g : Space n → ℂ := fun ξ => m ξ • angularFourier f ξ
  have he : (fun ξ => m ξ • angularFourier (fun y => conj (f y)) ξ) =
      (fun ξ => conj (g (-ξ))) := by
    funext ξ
    rw [OAI.Analysis.Fourier.BochnerRiesz.angularFourier_conj]
    simp only [g, hm, Complex.real_smul, map_mul, Complex.conj_ofReal]
  rw [he, OAI.Analysis.Fourier.BochnerRiesz.angularInverse_conj, OAI.Analysis.Fourier.BochnerRiesz.angularInverse_neg, neg_neg]

theorem besselPotential_conj {n : ℕ} (s : ℝ) (f : Space n → ℂ) (x : Space n) :
    besselPotential s (fun y => conj (f y)) x = conj (besselPotential s f x) := by
  apply angular_real_even_multiplier_conj
  intro ξ
  simp only [norm_neg]

theorem logBesselPotential_conj {n : ℕ} (s B : ℝ) (f : Space n → ℂ) (x : Space n) :
    logBesselPotential s B (fun y => conj (f y)) x =
      conj (logBesselPotential s B f x) := by
  apply angular_real_even_multiplier_conj
  intro ξ
  simp only [norm_neg]

theorem eLpNorm_besselPotential_schwartzConj {n : ℕ}
    (s : ℝ) (f : SchwartzMap (Space n) ℂ) (p : ℝ≥0∞) :
    eLpNorm (besselPotential s (OAI.Analysis.Fourier.BochnerRiesz.schwartzConj f)) p volume =
      eLpNorm (besselPotential s f) p volume := by
  have he : besselPotential s (OAI.Analysis.Fourier.BochnerRiesz.schwartzConj f) =
      (fun x => conj (besselPotential s f x)) := funext (besselPotential_conj s f)
  rw [he]
  exact eLpNorm_conj (besselPotential s f) p volume

theorem eLpNorm_logBesselPotential_schwartzConj {n : ℕ}
    (s B : ℝ) (f : SchwartzMap (Space n) ℂ) (p : ℝ≥0∞) :
    eLpNorm (logBesselPotential s B (OAI.Analysis.Fourier.BochnerRiesz.schwartzConj f)) p volume =
      eLpNorm (logBesselPotential s B f) p volume := by
  have he : logBesselPotential s B (OAI.Analysis.Fourier.BochnerRiesz.schwartzConj f) =
      (fun x => conj (logBesselPotential s B f x)) := funext (logBesselPotential_conj s B f)
  rw [he]
  exact eLpNorm_conj (logBesselPotential s B f) p volume

theorem eLpNorm_halfWave_schwartzConj {n : ℕ}
    (f : SchwartzMap (Space n) ℂ) (p : ℝ≥0∞) :
    eLpNorm (fun z : Space n × ℝ => halfWaveIntegral z.2 (OAI.Analysis.Fourier.BochnerRiesz.schwartzConj f) z.1)
      p (observationMeasure n) =
    eLpNorm (fun z : Space n × ℝ => halfWaveIntegral (-z.2) f z.1)
      p (observationMeasure n) := by
  have he : (fun z : Space n × ℝ => halfWaveIntegral z.2 (OAI.Analysis.Fourier.BochnerRiesz.schwartzConj f) z.1) =
      (fun z => conj (halfWaveIntegral (-z.2) f z.1)) := by
    funext z
    exact OAI.Analysis.Fourier.BochnerRiesz.halfWaveIntegral_conj f z.2 z.1
  rw [he]
  exact eLpNorm_conj (fun z : Space n × ℝ => halfWaveIntegral (-z.2) f z.1)
    p (observationMeasure n)

theorem frequencyHalfWave_conj {n : ℕ} (φ f : Space n → ℂ) (h t : ℝ) (x : Space n) :
    frequencyHalfWave (fun ξ => conj (φ (-ξ))) h t (fun y => conj (f y)) x =
      conj (frequencyHalfWave φ h (-t) f x) := by
  let g : Space n → ℂ := fun ξ => Complex.exp (-Complex.I * ((-t) * ‖ξ‖ : ℝ)) *
    φ (h • ξ) * angularFourier f ξ
  have he : (fun ξ => Complex.exp (-Complex.I * (t * ‖ξ‖ : ℝ)) *
      conj (φ (-(h • ξ))) * angularFourier (fun y => conj (f y)) ξ) =
      (fun ξ => conj (g (-ξ))) := by
    funext ξ
    rw [OAI.Analysis.Fourier.BochnerRiesz.angularFourier_conj]
    simp [g, ← Complex.exp_conj, smul_neg]
  rw [frequencyHalfWave, he, OAI.Analysis.Fourier.BochnerRiesz.angularInverse_conj,
    OAI.Analysis.Fourier.BochnerRiesz.angularInverse_neg, neg_neg]
  rfl

theorem eLpNorm_frequencyHalfWave_schwartzConj {n : ℕ} (φ : Space n → ℂ)
    (h : ℝ) (f : SchwartzMap (Space n) ℂ) (p : ℝ≥0∞) :
    eLpNorm (fun z : Space n × ℝ => frequencyHalfWave (fun ξ => conj (φ (-ξ)))
      h z.2 (OAI.Analysis.Fourier.BochnerRiesz.schwartzConj f) z.1) p (observationMeasure n) =
    eLpNorm (fun z : Space n × ℝ => frequencyHalfWave φ h (-z.2) f z.1)
      p (observationMeasure n) := by
  have he : (fun z : Space n × ℝ => frequencyHalfWave (fun ξ => conj (φ (-ξ)))
      h z.2 (OAI.Analysis.Fourier.BochnerRiesz.schwartzConj f) z.1) =
      (fun z => conj (frequencyHalfWave φ h (-z.2) f z.1)) := by
    funext z
    exact frequencyHalfWave_conj φ f h z.2 z.1
  rw [he]
  exact eLpNorm_conj (fun z : Space n × ℝ => frequencyHalfWave φ h (-z.2) f z.1)
    p (observationMeasure n)

/-- The logarithmic critical estimate also holds for the positive phase,
without requiring the frequency cutoff to be real or even. -/
theorem logarithmicRefinement_negative (hlog : LogarithmicRefinement)
    {n : ℕ} (hn : 2 ≤ n) (φ : Space n → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hz : 0 ∉ tsupport φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (fun z : Space n × ℝ => frequencyHalfWave φ h (-z.2) f z.1)
        (ENNReal.ofReal (criticalExponent n)) (observationMeasure n) ∧
      eLpNorm (fun z : Space n × ℝ => frequencyHalfWave φ h (-z.2) f z.1)
        (ENNReal.ofReal (criticalExponent n)) (observationMeasure n) ≤
      ENNReal.ofReal (C * (1 + Real.log (1 / h)) ^ (2 * n + 5)) *
        eLpNorm f (ENNReal.ofReal (criticalExponent n)) volume := by
  let ψ : Space n → ℂ := fun ξ => conj (φ (-ξ))
  have hd : ContDiff ℝ ∞ ψ :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp (hφ.comp contDiff_neg)
  have hcn : HasCompactSupport (fun ξ : Space n => φ (-ξ)) := by
    simpa only [neg_one_smul] using hc.comp_smul (show (-1 : ℝ) ≠ 0 by norm_num)
  have hcs : HasCompactSupport ψ := hcn.comp_left (map_zero (starRingEnd ℂ))
  have hzs : (0 : Space n) ∉ tsupport ψ := by
    apply notMem_tsupport_iff_eventuallyEq.mpr
    have H := (notMem_tsupport_iff_eventuallyEq.mp hz).comp_tendsto
      (show Filter.Tendsto (fun ξ : Space n => -ξ) (𝓝 0) (𝓝 0) by
        simpa only [neg_zero] using continuous_neg.tendsto (0 : Space n))
    filter_upwards [H] with ξ hξ
    change φ (-ξ) = 0 at hξ
    change conj (φ (-ξ)) = 0
    rw [hξ, map_zero]
  obtain ⟨C, hC, hb⟩ := hlog n hn ψ hd hcs hzs
  refine ⟨C, hC, fun h hh h1 f => ?_⟩
  obtain ⟨hm, hbnd⟩ := hb h hh h1 (OAI.Analysis.Fourier.BochnerRiesz.schwartzConj f)
  change eLpNorm _ _ _ < ⊤ at hm
  change eLpNorm (fun z : Space n × ℝ => frequencyHalfWave
    (fun ξ => conj (φ (-ξ))) h z.2 (OAI.Analysis.Fourier.BochnerRiesz.schwartzConj f) z.1) _ _ < ⊤ at hm
  rw [eLpNorm_frequencyHalfWave_schwartzConj] at hm
  change eLpNorm (fun z : Space n × ℝ => frequencyHalfWave
    (fun ξ => conj (φ (-ξ))) h z.2 (OAI.Analysis.Fourier.BochnerRiesz.schwartzConj f) z.1) _ _ ≤ _ at hbnd
  rw [eLpNorm_frequencyHalfWave_schwartzConj, OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_schwartzConj] at hbnd
  exact ⟨hm, hbnd⟩

/-- The positive-phase propagator has the same Sobolev estimate, with the
same constant, as its negative-phase counterpart. -/
theorem euclideanLocalSmoothing_negative (hls : EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {p ε : ℝ} (hp : 2 ≤ p)
    (hε : 0 < ε ∨ (p = 2 ∧ ε = 0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (besselPotential (smoothingOrder n p + ε) f) (ENNReal.ofReal p) ∧
      MemLp (fun z : Space n × ℝ => halfWaveIntegral (-z.2) f z.1)
        (ENNReal.ofReal p) (observationMeasure n) ∧
      eLpNorm (fun z : Space n × ℝ => halfWaveIntegral (-z.2) f z.1)
        (ENNReal.ofReal p) (observationMeasure n) ≤
      ENNReal.ofReal C * eLpNorm (besselPotential (smoothingOrder n p + ε) f)
        (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hb⟩ := hls n hn p ε hp hε
  refine ⟨C, hC, fun f => ?_⟩
  obtain ⟨hJ, hW, hbound⟩ := hb (OAI.Analysis.Fourier.BochnerRiesz.schwartzConj f)
  change eLpNorm _ _ _ < ⊤ at hJ hW
  rw [eLpNorm_besselPotential_schwartzConj] at hJ
  rw [eLpNorm_halfWave_schwartzConj] at hW
  rw [eLpNorm_halfWave_schwartzConj, eLpNorm_besselPotential_schwartzConj] at hbound
  exact ⟨hJ, hW, hbound⟩

/-- Time reversal also preserves the exact logarithmically corrected
Sobolev order; no extra derivative loss is introduced. -/
theorem logarithmicSobolev_negative (hlog : LogarithmicSobolev)
    {n : ℕ} (hn : 2 ≤ n) {p B : ℝ} (hp : 2 < p) (hB : 2 * n + 6 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (logBesselPotential (smoothingOrder n p) B f) (ENNReal.ofReal p) ∧
      MemLp (fun z : Space n × ℝ => halfWaveIntegral (-z.2) f z.1)
        (ENNReal.ofReal p) (observationMeasure n) ∧
      eLpNorm (fun z : Space n × ℝ => halfWaveIntegral (-z.2) f z.1)
        (ENNReal.ofReal p) (observationMeasure n) ≤
      ENNReal.ofReal C * eLpNorm (logBesselPotential (smoothingOrder n p) B f)
        (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hb⟩ := hlog n hn p B hp hB
  refine ⟨C, hC, fun f => ?_⟩
  obtain ⟨hJ, hW, hbound⟩ := hb (OAI.Analysis.Fourier.BochnerRiesz.schwartzConj f)
  change eLpNorm _ _ _ < ⊤ at hJ hW
  rw [eLpNorm_logBesselPotential_schwartzConj] at hJ
  rw [eLpNorm_halfWave_schwartzConj] at hW
  rw [eLpNorm_halfWave_schwartzConj, eLpNorm_logBesselPotential_schwartzConj] at hbound
  exact ⟨hJ, hW, hbound⟩

end OAI.Analysis.Fourier.LocalSmoothing
