import OAI.Analysis.Fourier.LocalSmoothing.Definitions

open OAI.Analysis.Fourier.Wave

/-! # Bochner–Riesz multipliers and critical indices -/

open _root_.MeasureTheory
open scoped RealInnerProductSpace ENNReal

noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

def bochnerRieszSymbol {n : ℕ} (δ R : ℝ) (ξ : Space n) : ℝ :=
  (max (1 - (‖ξ‖ / R) ^ 2) 0) ^ δ

def bochnerRiesz {n : ℕ} (δ R : ℝ) (f : Space n → ℂ) : Space n → ℂ :=
  OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ bochnerRieszSymbol δ R ξ • OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ)

def bochnerRieszMaximal {n : ℕ} (δ : ℝ) (f : Space n → ℂ) (x : Space n) : ℝ≥0∞ :=
  ⨆ R : ℝ, ⨆ (_ : 0 < R), ‖bochnerRiesz δ R f x‖ₑ

/-- The critical index for all input exponents, including `∞`. -/
def bochnerRieszIndex (n : ℕ) (p : ℝ≥0∞) : ℝ :=
  max ((n : ℝ) * |(p⁻¹).toReal - 1 / 2| - 1 / 2) 0

def BochnerRieszConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ p : ℝ≥0∞, 1 ≤ p → ∀ δ : ℝ,
    bochnerRieszIndex n p < δ → ∃ C : ℝ, 0 < C ∧
      ∀ R : ℝ, 0 < R → ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (bochnerRiesz δ R f) p ∧
      eLpNorm (bochnerRiesz δ R f) p volume ≤
        ENNReal.ofReal C * eLpNorm f p volume

def MaximalBochnerRieszConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ p δ : ℝ, 2 ≤ p → OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p < δ →
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (bochnerRieszMaximal δ f) (ENNReal.ofReal p) ∧
      eLpNorm (bochnerRieszMaximal δ f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume

end OAI.Analysis.Fourier.BochnerRiesz
