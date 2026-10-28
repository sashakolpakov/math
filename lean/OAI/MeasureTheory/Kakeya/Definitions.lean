import OAI.Analysis.Fourier.LocalSmoothing.Definitions
import OAI.Analysis.Fourier.Restriction.Definitions
import Mathlib.Topology.MetricSpace.HausdorffDimension

open OAI.Analysis.Fourier.Wave

/-! # Unit tubes, the Kakeya maximal operator, and Kakeya sets -/

open _root_.MeasureTheory
open scoped RealInnerProductSpace ENNReal

noncomputable section
namespace OAI.MeasureTheory.Kakeya

def unitSegment {n : ℕ} (ω x : Space n) : Set (Space n) :=
  {y | ∃ t ∈ Set.Icc (- (1 / 2 : ℝ)) (1 / 2), y = x + t • ω}

/-- Open radius-`δ` neighbourhood of a unit segment when `‖ω‖ = 1`. -/
def tube {n : ℕ} (δ : ℝ) (ω x : Space n) : Set (Space n) :=
  ⋃ t ∈ Set.Icc (- (1 / 2 : ℝ)) (1 / 2), Metric.ball (x + t • ω) δ

def kakeyaMaximal {n : ℕ} (δ : ℝ) (f : Space n → ℂ) (ω : Space n) : ℝ≥0∞ :=
  ⨆ x : Space n,
    (∫⁻ y in tube δ ω x, ‖f y‖ₑ) / volume (tube δ ω x)

def KakeyaMaximalConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ f : Space n → ℂ, MemLp f n →
    MemLp (kakeyaMaximal δ f) n (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ∧
    eLpNorm (kakeyaMaximal δ f) n (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      ENNReal.ofReal (C * δ ^ (-ε)) * eLpNorm f n volume

def IsKakeyaSet {n : ℕ} (F : Set (Space n)) : Prop :=
  ∀ ω : Space n, ‖ω‖ = 1 → ∃ x, unitSegment ω x ⊆ F

def KakeyaConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ F : Set (Space n), IsKakeyaSet F →
    dimH F = n

end OAI.MeasureTheory.Kakeya
