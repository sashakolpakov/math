import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.CriticalNorm

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

open _root_.MeasureTheory
open scoped ENNReal

/-- The explicit initial-packet estimate, kept as a short interface for
the two scalar sharpness arguments. The actual estimate is proved in
`SharpnessInputLp`. -/
def PacketInputBound (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 1 ≤ p → ∀ N : ℝ, 2 ≤ N →
    ∀ f : SchwartzMap (Space n) ℂ,
    (f : Space n → ℂ) = OAI.Analysis.Fourier.LocalSmoothing.angularInverse (focusingSymbol n N (3/2)) →
    eLpNorm f (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (C*N^((n:ℝ)-radialOrder n-1/p))

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
