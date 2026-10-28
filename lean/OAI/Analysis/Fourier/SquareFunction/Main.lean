import OAI.Analysis.Fourier.LocalSmoothing.Main
import OAI.Analysis.Fourier.SquareFunction.LocalSmoothing
import OAI.Analysis.Fourier.SquareFunction.Square.ExtensionLocalSmoothing

/-! # Stein square-function estimates and their full Lp extension -/

noncomputable section
namespace OAI.Analysis.Fourier.SquareFunction

/-- The estimate in Theorem `thm:stein-square` throughout its strict range. -/
theorem stein_square : SteinSquareConjecture :=
  localSmoothing_steinSquareConjecture LocalSmoothing.euclidean_local_smoothing

/-- The density clause of the Stein theorem, with the actual unique
continuous square-function extension to every finite Lp in the strict range. -/
def SteinSquareFullLp : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ p : ENNReal, ∀ [Fact (1 ≤ p)],
    p ≠ ⊤ → 2 ≤ p.toReal → ∀ α : ℝ,
    max (1/2) ((n:ℝ) * (1/2 - 1/p.toReal)) < α →
      Nonempty (SquareLpExtension n α p)

theorem stein_square_fullLp : SteinSquareFullLp := by
  intro n hn p hp hptop hp2 α hα
  exact localSmoothing_squareLpExtension LocalSmoothing.euclidean_local_smoothing hn hptop hp2 hα

end OAI.Analysis.Fourier.SquareFunction
