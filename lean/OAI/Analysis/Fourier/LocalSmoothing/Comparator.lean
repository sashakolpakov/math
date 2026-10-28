import OAI.Analysis.Fourier.SquareFunction.Square.Literal

/-!
# Comparator solution

The definitions below deliberately mirror the Mathlib-only reference in one
compilation unit, so Lean's generated auxiliary declarations match as well.
This file does not import `Challenge`; its six proofs use the existing development.
-/

open _root_.MeasureTheory
open scoped RealInnerProductSpace ENNReal

noncomputable section

namespace OAI.Analysis.Fourier.LocalSmoothing.Comparator

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def angularFourier {n : ℕ} (f : Space n → ℂ) (ξ : Space n) : ℂ :=
  ∫ x, Complex.exp (-Complex.I * ((inner ℝ x ξ : ℝ) : ℂ)) * f x

def angularInverse {n : ℕ} (g : Space n → ℂ) (x : Space n) : ℂ :=
  (((2 * Real.pi) ^ n)⁻¹ : ℝ) •
    ∫ ξ, Complex.exp (Complex.I * ((inner ℝ x ξ : ℝ) : ℂ)) * g ξ

def halfWaveIntegral {n : ℕ} (t : ℝ) (f : Space n → ℂ) : Space n → ℂ :=
  angularInverse (fun ξ ↦ Complex.exp (-Complex.I * (t * ‖ξ‖ : ℝ)) *
    angularFourier f ξ)

def besselPotential {n : ℕ} (s : ℝ) (f : Space n → ℂ) : Space n → ℂ :=
  angularInverse (fun ξ ↦ ((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) • angularFourier f ξ)

def observationMeasure (n : ℕ) : Measure (Space n × ℝ) :=
  volume.prod (volume.restrict (Set.Icc 1 2))

namespace Implications

/-- Surface measure on the unit sphere, viewed as a measure on ambient space. -/
def sphereMeasure (n : ℕ) : Measure (Space n) :=
  (volume : Measure (Space n)).toSphere.map Subtype.val

def sphericalExtension {n : ℕ} (g : Space n → ℂ) (x : Space n) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * ((inner ℝ x ω : ℝ) : ℂ)) * g ω ∂sphereMeasure n

def conjugateExponent (a : ℝ≥0∞) : ℝ :=
  if a = ∞ then 1 else a.toReal / (a.toReal - 1)

def bochnerRieszSymbol {n : ℕ} (δ R : ℝ) (ξ : Space n) : ℝ :=
  (max (1 - (‖ξ‖ / R) ^ 2) 0) ^ δ

def bochnerRiesz {n : ℕ} (δ R : ℝ) (f : Space n → ℂ) : Space n → ℂ :=
  angularInverse (fun ξ ↦ bochnerRieszSymbol δ R ξ • angularFourier f ξ)

def unitSegment {n : ℕ} (ω x : Space n) : Set (Space n) :=
  {y | ∃ t ∈ Set.Icc (- (1 / 2 : ℝ)) (1 / 2), y = x + t • ω}

/-- Open radius-`δ` neighbourhood of the unit segment in direction `ω`. -/
def tube {n : ℕ} (δ : ℝ) (ω x : Space n) : Set (Space n) :=
  ⋃ t ∈ Set.Icc (- (1 / 2 : ℝ)) (1 / 2), Metric.ball (x + t • ω) δ

def kakeyaMaximal {n : ℕ} (δ : ℝ) (f : Space n → ℂ) (ω : Space n) : ℝ≥0∞ :=
  ⨆ x : Space n,
    (∫⁻ y in tube δ ω x, ‖f y‖ₑ) / volume (tube δ ω x)

def IsKakeyaSet {n : ℕ} (F : Set (Space n)) : Prop :=
  ∀ ω : Space n, ‖ω‖ = 1 → ∃ x, unitSegment ω x ⊆ F

end Implications

namespace Stein

/-- The square function with the actual radius derivative `r ∂ᵣ Bᵅᵣ f`. -/
def literalSteinSquareFunction {n : ℕ} (α : ℝ) (f : Space n → ℂ)
    (x : Space n) : ℝ≥0∞ :=
  (∫⁻ r in Set.Ioi (0 : ℝ),
    ‖r • deriv (fun s => Implications.bochnerRiesz α s f x) r‖ₑ ^ 2 /
      ENNReal.ofReal r) ^ (1 / 2 : ℝ)

end Stein

open OAI.Analysis.Fourier.LocalSmoothing.Comparator.Implications

/-- Local smoothing for every finite `p ≥ 2`, including zero loss at `p = 2`. -/
theorem euclidean_local_smoothing :
    ∀ n : ℕ, 2 ≤ n → ∀ p ε : ℝ, 2 ≤ p → (0 < ε ∨ (p = 2 ∧ ε = 0)) →
      ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
        MemLp (besselPotential (max 0 (((n : ℝ) - 1) / 2 - n / p) + ε) f)
          (ENNReal.ofReal p) ∧
        MemLp (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1)
          (ENNReal.ofReal p) (observationMeasure n) ∧
        eLpNorm (fun z : Space n × ℝ ↦ halfWaveIntegral z.2 f z.1)
          (ENNReal.ofReal p) (observationMeasure n) ≤
        ENNReal.ofReal C *
          eLpNorm (besselPotential (max 0 (((n : ℝ) - 1) / 2 - n / p) + ε) f)
            (ENNReal.ofReal p) volume := by
  exact OAI.Analysis.Fourier.LocalSmoothing.euclidean_local_smoothing

/-- Uniform Bochner–Riesz bounds in the full strict range, including `p = ∞`. -/
theorem bochner_riesz :
    ∀ n : ℕ, 2 ≤ n → ∀ p : ℝ≥0∞, 1 ≤ p → ∀ δ : ℝ,
      max ((n : ℝ) * |(p⁻¹).toReal - 1 / 2| - 1 / 2) 0 < δ →
      ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R → ∀ f : SchwartzMap (Space n) ℂ,
        MemLp (bochnerRiesz δ R f) p ∧
        eLpNorm (bochnerRiesz δ R f) p volume ≤
          ENNReal.ofReal C * eLpNorm f p volume := by
  exact OAI.Analysis.Fourier.BochnerRiesz.bochner_riesz_schwartz

/-- Spherical restriction in extension form, throughout the strict mixed range. -/
theorem spherical_restriction :
    ∀ n : ℕ, 2 ≤ n → ∀ a : ℝ≥0∞, 1 < a → ∀ b : ℝ,
      2 * (n : ℝ) / (n - 1) < b →
      ((n : ℝ) + 1) / ((n : ℝ) - 1) * conjugateExponent a < b →
      ∃ C : ℝ, 0 < C ∧ ∀ g : Space n → ℂ, MemLp g a (sphereMeasure n) →
        MemLp (sphericalExtension g) (ENNReal.ofReal b) ∧
        eLpNorm (sphericalExtension g) (ENNReal.ofReal b) volume ≤
          ENNReal.ofReal C * eLpNorm g a (sphereMeasure n) := by
  exact OAI.Analysis.Fourier.Restriction.spherical_restriction

/-- Kakeya maximal bounds with every positive epsilon loss, uniformly in scale. -/
theorem kakeya_maximal :
    ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ f : Space n → ℂ, MemLp f n →
        MemLp (kakeyaMaximal δ f) n (sphereMeasure n) ∧
        eLpNorm (kakeyaMaximal δ f) n (sphereMeasure n) ≤
          ENNReal.ofReal (C * δ ^ (-ε)) * eLpNorm f n volume := by
  exact OAI.MeasureTheory.Kakeya.kakeya_maximal

/-- Every Kakeya set has full Hausdorff dimension; no measurability is assumed. -/
theorem kakeya :
    ∀ n : ℕ, 2 ≤ n → ∀ F : Set (Space n), IsKakeyaSet F → dimH F = n := by
  exact OAI.MeasureTheory.Kakeya.kakeya

/-- Stein's square-function estimate throughout the conjectured strict range. -/
theorem stein_square :
    ∀ n : ℕ, 2 ≤ n → ∀ p α : ℝ, 2 ≤ p →
      max (1 / 2) ((n : ℝ) * (1 / 2 - 1 / p)) < α →
      ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
        MemLp (Stein.literalSteinSquareFunction α f) (ENNReal.ofReal p) volume ∧
        eLpNorm (Stein.literalSteinSquareFunction α f) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume := by
  intro n hn p α hp hα
  exact OAI.Analysis.Fourier.SquareFunction.stein_square_literal hn hp hα

end OAI.Analysis.Fourier.LocalSmoothing.Comparator
