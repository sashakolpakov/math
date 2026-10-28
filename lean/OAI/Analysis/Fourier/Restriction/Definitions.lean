import OAI.Analysis.Fourier.LocalSmoothing.Definitions
import Mathlib.MeasureTheory.Constructions.HaarToSphere

open OAI.Analysis.Fourier.Wave

/-! # Spherical measure, extension, and the strict restriction range -/

open _root_.MeasureTheory
open scoped RealInnerProductSpace ENNReal

noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- Euclidean surface measure obtained by polar disintegration of Lebesgue
measure, represented on the ambient Euclidean space. -/
def sphereMeasure (n : ℕ) : Measure (Space n) :=
  (volume : Measure (Space n)).toSphere.map Subtype.val

def sphericalExtension {n : ℕ} (g : Space n → ℂ) (x : Space n) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * ((inner ℝ x ω : ℝ) : ℂ)) * g ω ∂sphereMeasure n

/-- Conjugate exponent, including the input exponent `∞`. -/
def conjugateExponent (a : ℝ≥0∞) : ℝ :=
  if a = ∞ then 1 else a.toReal / (a.toReal - 1)

def SphericalRestrictionConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ a : ℝ≥0∞, 1 < a → ∀ b : ℝ,
    OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n < b →
    ((n : ℝ) + 1) / ((n : ℝ) - 1) * conjugateExponent a < b →
    ∃ C : ℝ, 0 < C ∧ ∀ g : Space n → ℂ, MemLp g a (sphereMeasure n) →
      MemLp (sphericalExtension g) (ENNReal.ofReal b) ∧
      eLpNorm (sphericalExtension g) (ENNReal.ofReal b) volume ≤
        ENNReal.ofReal C * eLpNorm g a (sphereMeasure n)

end OAI.Analysis.Fourier.Restriction
