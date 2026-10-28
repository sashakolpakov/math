import OAI.Analysis.Fourier.Dispersion.Elliptic

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.Dispersion

/-- The source's literal positive quadratic Klein–Gordon/wave propagator. -/
def quadraticHalfWave {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (m t : ℝ)
    (f : Space n → ℂ) (x : Space n) : ℂ :=
  dispersionIntegral (quadraticDispersion Q m) t f x

/-- Source `cor:constant-dispersion`, local smoothing including the zero-loss L² endpoint. -/
def ConstantEllipticLocalSmoothing : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ Q : Matrix (Fin n) (Fin n) ℝ, Q.PosDef →
    ∀ m : ℝ, 0 ≤ m → ∀ p ε : ℝ, 2 ≤ p → (0 < ε ∨ (p = 2 ∧ ε = 0)) →
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (OAI.Analysis.Fourier.LocalSmoothing.besselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p+ε) f) (ENNReal.ofReal p) volume ∧
      MemLp (fun z : Space n × ℝ ↦ quadraticHalfWave Q m z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ∧
      eLpNorm (fun z : Space n × ℝ ↦ quadraticHalfWave Q m z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal C * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.besselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p+ε) f) (ENNReal.ofReal p) volume

/-- Source `cor:constant-dispersion`, with the unchanged logarithmic power. -/
def ConstantEllipticLogarithmicSobolev : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ Q : Matrix (Fin n) (Fin n) ℝ, Q.PosDef →
    ∀ m : ℝ, 0 ≤ m → ∀ p B : ℝ, 2 < p → 2 * (n : ℝ) + 6 < B →
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p) B f) (ENNReal.ofReal p) volume ∧
      MemLp (fun z : Space n × ℝ ↦ quadraticHalfWave Q m z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ∧
      eLpNorm (fun z : Space n × ℝ ↦ quadraticHalfWave Q m z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal C * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p) B f) (ENNReal.ofReal p) volume

theorem constantEllipticLocalSmoothing_of_logarithmicRefinement
    (hlog : OAI.Analysis.Fourier.LocalSmoothing.LogarithmicRefinement) : ConstantEllipticLocalSmoothing := by
  intro n hn Q hQ m hm p ε hp hε
  obtain ⟨R,hR⟩ := quadraticDispersion_eq_radial_comp Q hQ
  have hf := linearMassDispersion_frequency_bound hlog hn R m hp
    (OAI.Analysis.Fourier.LocalSmoothing.contDiff_smoothingAnnularCutoff n) (OAI.Analysis.Fourier.LocalSmoothing.hasCompactSupport_smoothingAnnularCutoff n)
    (OAI.Analysis.Fourier.LocalSmoothing.zero_notMem_tsupport_smoothingAnnularCutoff n)
  have H := dispersion_localSmoothing_of_frequency_bound (continuous_linearMassDispersion R m)
    hp hε hf (fun χ hχ hc ↦ linearMassDispersion_uniform_kernel R m hχ hc)
  have he : quadraticDispersion Q m = linearMassDispersion R m := hR m
  simpa only [quadraticHalfWave,he] using H

theorem constantEllipticLogarithmicSobolev_of_logarithmicRefinement
    (hlog : OAI.Analysis.Fourier.LocalSmoothing.LogarithmicRefinement) : ConstantEllipticLogarithmicSobolev := by
  intro n hn Q hQ m hm p B hp hB
  obtain ⟨R,hR⟩ := quadraticDispersion_eq_radial_comp Q hQ
  have hf := linearMassDispersion_frequency_bound hlog hn R m hp.le
    (OAI.Analysis.Fourier.LocalSmoothing.contDiff_smoothingAnnularCutoff n) (OAI.Analysis.Fourier.LocalSmoothing.hasCompactSupport_smoothingAnnularCutoff n)
    (OAI.Analysis.Fourier.LocalSmoothing.zero_notMem_tsupport_smoothingAnnularCutoff n)
  have H := dispersion_logarithmicSobolev_of_frequency_bound (continuous_linearMassDispersion R m)
    hp hB hf (fun χ hχ hc ↦ linearMassDispersion_uniform_kernel R m hχ hc)
  have he : quadraticDispersion Q m = linearMassDispersion R m := hR m
  simpa only [quadraticHalfWave,he] using H

end OAI.Analysis.Fourier.Dispersion
