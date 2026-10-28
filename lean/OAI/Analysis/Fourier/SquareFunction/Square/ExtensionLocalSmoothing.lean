import OAI.Analysis.Fourier.SquareFunction.Square.Extension

noncomputable section
open _root_.MeasureTheory Set Filter
open scoped ENNReal Topology
namespace OAI.Analysis.Fourier.SquareFunction

/-- The density clause of the strict Stein square-function theorem: a
genuine, unique continuous operator on all Lp, agreeing with the radius
square function on Schwartz functions. -/
theorem localSmoothing_squareLpExtension (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp2 : 2 ≤ p.toReal) {α : ℝ}
    (hα : max (1 / 2) ((n : ℝ) * (1 / 2 - 1 / p.toReal)) < α) :
    Nonempty (SquareLpExtension n α p) := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨C,hC,hb⟩ := localSmoothing_steinSquareConjecture hls n hn p.toReal α hp2 hα
  apply exists_squareLpExtension_of_bound hp ((le_max_left _ _).trans_lt hα) hC
  intro f
  simpa only [ENNReal.ofReal_toReal hp] using (hb f).2

/-- Real-exponent formulation of the full-Lp extension theorem. -/
theorem localSmoothing_squareLpExtension_real (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {p α : ℝ} (hp : 2 ≤ p)
    (hα : max (1 / 2) ((n : ℝ) * (1 / 2 - 1 / p)) < α) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show 1 ≤ p by linarith)⟩
    Nonempty (SquareLpExtension n α (ENNReal.ofReal p)) := by
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show 1 ≤ p by linarith)⟩
  apply localSmoothing_squareLpExtension hls hn (p := ENNReal.ofReal p) ENNReal.ofReal_ne_top
  · simpa only [ENNReal.toReal_ofReal (show 0 ≤ p by linarith)] using hp
  · simpa only [ENNReal.toReal_ofReal (show 0 ≤ p by linarith)] using hα

end OAI.Analysis.Fourier.SquareFunction
