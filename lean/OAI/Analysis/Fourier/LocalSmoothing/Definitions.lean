import OAI.Analysis.Fourier.Wave.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic

open OAI.Analysis.Fourier.Wave

/-!
Exact analytic targets from `sections/introduction.tex`.

These are propositions, not asserted theorems. Their proofs require the current,
Dirichlet, concentration, and transfer constructions. Fourier integrals use the
angular-frequency normalization of the manuscript. Extended norms retain
infinite values; the hypotheses and conclusions explicitly require integrability
where needed.
-/

open _root_.MeasureTheory
open scoped RealInnerProductSpace ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing

def criticalExponent (n : ℕ) : ℝ := 2 * n / (n - 1)
def smoothingOrder (n : ℕ) (p : ℝ) : ℝ := max 0 (((n : ℝ) - 1) / 2 - n / p)

/-- The angular-frequency Fourier transform in the introduction. -/
def angularFourier {n : ℕ} (f : Space n → ℂ) (ξ : Space n) : ℂ :=
  ∫ x, Complex.exp (-Complex.I * ((inner ℝ x ξ : ℝ) : ℂ)) * f x

def angularInverse {n : ℕ} (g : Space n → ℂ) (x : Space n) : ℂ :=
  (((2 * Real.pi) ^ n)⁻¹ : ℝ) •
    ∫ ξ, Complex.exp (Complex.I * ((inner ℝ x ξ : ℝ) : ℂ)) * g ξ

/-- The exact oscillatory integral defining `U(t)` in the manuscript. -/
def halfWaveIntegral {n : ℕ} (t : ℝ) (f : Space n → ℂ) : Space n → ℂ :=
  angularInverse (fun ξ ↦ Complex.exp (-Complex.I * (t * ‖ξ‖ : ℝ)) *
    angularFourier f ξ)

/-- The multiplier `J^s`, with `J = (I - Δ)^(1/2)`. -/
def besselPotential {n : ℕ} (s : ℝ) (f : Space n → ℂ) : Space n → ℂ :=
  angularInverse (fun ξ ↦ ((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) • angularFourier f ξ)

/-- The multiplier `J^s [log(2+J)]^B`. -/
def logBesselPotential {n : ℕ} (s B : ℝ) (f : Space n → ℂ) : Space n → ℂ :=
  angularInverse (fun ξ ↦
    ((1 + ‖ξ‖ ^ 2) ^ (s / 2) *
      Real.log (2 + Real.sqrt (1 + ‖ξ‖ ^ 2)) ^ B : ℝ) • angularFourier f ξ)

def frequencyHalfWave {n : ℕ} (φ : Space n → ℂ) (h t : ℝ)
    (f : Space n → ℂ) : Space n → ℂ :=
  angularInverse (fun ξ ↦ Complex.exp (-Complex.I * (t * ‖ξ‖ : ℝ)) *
    φ (h • ξ) * angularFourier f ξ)

def observationMeasure (n : ℕ) : Measure (Space n × ℝ) :=
  volume.prod (volume.restrict (Set.Icc 1 2))

/-- Theorem `thm:local-smoothing`, including the zero-loss `p=2` case.
No local-smoothing estimate is included as a hypothesis. -/
def EuclideanLocalSmoothing : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ p ε : ℝ, 2 ≤ p → (0 < ε ∨ (p = 2 ∧ ε = 0)) →
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (besselPotential (smoothingOrder n p + ε) f) (ENNReal.ofReal p) ∧
      MemLp (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal p) (observationMeasure n) ∧
      eLpNorm (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal p) (observationMeasure n) ≤
      ENNReal.ofReal C *
        eLpNorm (besselPotential (smoothingOrder n p + ε) f) (ENNReal.ofReal p) volume

/-- Theorem `thm:main`, with compactly supported smooth cutoffs away from zero. -/
def LogarithmicRefinement : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ φ : Space n → ℂ,
    ContDiff ℝ ∞ φ → HasCompactSupport φ → 0 ∉ tsupport φ →
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (fun z : Space n × ℝ ↦ frequencyHalfWave φ h z.2 f z.1)
        (ENNReal.ofReal (criticalExponent n)) (observationMeasure n) ∧
      eLpNorm (fun z : Space n × ℝ ↦ frequencyHalfWave φ h z.2 f z.1)
        (ENNReal.ofReal (criticalExponent n)) (observationMeasure n) ≤
      ENNReal.ofReal (C * (1 + Real.log (1 / h)) ^ (2 * n + 5)) *
        eLpNorm f (ENNReal.ofReal (criticalExponent n)) volume

/-- Corollary `cor:log-sobolev`. -/
def LogarithmicSobolev : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ p B : ℝ, 2 < p → 2 * n + 6 < B →
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (logBesselPotential (smoothingOrder n p) B f) (ENNReal.ofReal p) ∧
      MemLp (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal p) (observationMeasure n) ∧
      eLpNorm (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal p) (observationMeasure n) ≤
      ENNReal.ofReal C *
        eLpNorm (logBesselPotential (smoothingOrder n p) B f) (ENNReal.ofReal p) volume

end OAI.Analysis.Fourier.LocalSmoothing
