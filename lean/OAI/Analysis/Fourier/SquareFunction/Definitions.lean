import OAI.Analysis.Fourier.LocalSmoothing.Definitions

open OAI.Analysis.Fourier.Wave

/-! # Radius derivatives and Stein's square function -/

open _root_.MeasureTheory
open scoped RealInnerProductSpace ENNReal

noncomputable section
namespace OAI.Analysis.Fourier.SquareFunction

def radiusDerivativeSymbol {n : ℕ} (α r : ℝ) (ξ : Space n) : ℝ :=
  if ‖ξ‖ < r then
    2 * α * (‖ξ‖ ^ 2 / r ^ 2) * (1 - ‖ξ‖ ^ 2 / r ^ 2) ^ (α - 1)
  else 0

def radiusDerivative {n : ℕ} (α r : ℝ) (f : Space n → ℂ) : Space n → ℂ :=
  OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ ↦ radiusDerivativeSymbol α r ξ • OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ)

/-- Squared-radius integral, kept in the extended nonnegative reals. -/
def steinSquareFunction {n : ℕ} (α : ℝ) (f : Space n → ℂ) (x : Space n) : ℝ≥0∞ :=
  (∫⁻ r in Set.Ioi (0 : ℝ), ‖radiusDerivative α r f x‖ₑ ^ 2 /
    ENNReal.ofReal r) ^ (1 / 2 : ℝ)

def SteinSquareConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ p α : ℝ, 2 ≤ p →
    max (1 / 2) ((n : ℝ) * (1 / 2 - 1 / p)) < α →
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (steinSquareFunction α f) (ENNReal.ofReal p) ∧
      eLpNorm (steinSquareFunction α f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume

end OAI.Analysis.Fourier.SquareFunction
