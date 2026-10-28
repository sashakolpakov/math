import OAI.Analysis.Fourier.SquareFunction.Radius.SymbolDerivative
import OAI.Analysis.Fourier.Main

open OAI.Analysis.Fourier.Wave

noncomputable section
open Set _root_.MeasureTheory
open scoped ENNReal

namespace OAI.Analysis.Fourier.SquareFunction

/-- The literal square function from the manuscript, using the actual
derivative of the Bochner--Riesz means with respect to their radius. -/
def literalSteinSquareFunction {n : ℕ} (α : ℝ) (f : Space n → ℂ)
    (x : Space n) : ℝ≥0∞ :=
  (∫⁻ r in Ioi (0 : ℝ),
    ‖r • deriv (fun s => OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz α s f x) r‖ₑ ^ 2 /
      ENNReal.ofReal r) ^ (1 / 2 : ℝ)

/-- The proved radius differentiation identity identifies the literal
square function pointwise, not merely almost everywhere. -/
theorem literalSteinSquareFunction_eq {n : ℕ} [NeZero n] {α : ℝ}
    (hα : 1 / 2 < α) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    literalSteinSquareFunction α f x = OAI.Analysis.Fourier.SquareFunction.steinSquareFunction α f x := by
  unfold literalSteinSquareFunction OAI.Analysis.Fourier.SquareFunction.steinSquareFunction
  congr 1
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [(OAI.Analysis.Fourier.SquareFunction.hasDerivAt_bochnerRiesz_radius hα hr f x).deriv,
    smul_smul,mul_inv_cancel₀ (ne_of_gt hr),one_smul]

theorem literalSteinSquareFunction_eq_fun {n : ℕ} [NeZero n] {α : ℝ}
    (hα : 1 / 2 < α) (f : SchwartzMap (Space n) ℂ) :
    literalSteinSquareFunction α f = OAI.Analysis.Fourier.SquareFunction.steinSquareFunction α f :=
  funext (literalSteinSquareFunction_eq hα f)

theorem measurable_literalSteinSquareFunction {n : ℕ} [NeZero n] {α : ℝ}
    (hα : 1 / 2 < α) (f : SchwartzMap (Space n) ℂ) :
    Measurable (literalSteinSquareFunction α f) := by
  rw [literalSteinSquareFunction_eq_fun hα f]
  exact measurable_steinSquareFunction α f

/-- The full-Lp extension agrees with the literal radius derivative formula
on the dense Schwartz class. Thus its continuous extension is also the
extension of the manuscript's actual square function. -/
theorem SquareLpExtension.schwartz_literal {n : ℕ} [NeZero n] {α : ℝ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (S : SquareLpExtension n α p)
    (hα : 1 / 2 < α) (f : SchwartzMap (Space n) ℂ) :
    ⇑(S.toFun (f.toLp p volume)) =ᵐ[volume]
      fun x => (literalSteinSquareFunction α f x).toReal := by
  filter_upwards [S.schwartz f] with x hx
  rw [hx,literalSteinSquareFunction_eq hα f]
  rfl

theorem SquareLpExtension.schwartz_literal_enorm {n : ℕ} [NeZero n] {α : ℝ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (S : SquareLpExtension n α p)
    (hα : 1 / 2 < α) (f : SchwartzMap (Space n) ℂ) :
    (fun x => ‖S.toFun (f.toLp p volume) x‖ₑ) =ᵐ[volume]
      literalSteinSquareFunction α f := by
  rw [literalSteinSquareFunction_eq_fun hα f]
  exact S.schwartz_enorm hα f

end OAI.Analysis.Fourier.SquareFunction
namespace OAI.Analysis.Fourier.SquareFunction

/-- The strict-range Stein square-function estimate with the actual
radius derivative appearing in the definition. -/
theorem stein_square_literal {n : ℕ} (hn : 2 ≤ n) {p α : ℝ} (hp : 2 ≤ p)
    (hα : max (1 / 2) ((n : ℝ) * (1 / 2 - 1 / p)) < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (OAI.Analysis.Fourier.SquareFunction.literalSteinSquareFunction α f) (ENNReal.ofReal p) volume ∧
      eLpNorm (OAI.Analysis.Fourier.SquareFunction.literalSteinSquareFunction α f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨C,hC,h⟩ := OAI.Analysis.Fourier.SquareFunction.stein_square n hn p α hp hα
  refine ⟨C,hC,fun f => ?_⟩
  simpa only [OAI.Analysis.Fourier.SquareFunction.literalSteinSquareFunction_eq_fun ((le_max_left _ _).trans_lt hα) f]
    using h f

/-- Density extension of the literal formula, with the already proved
Lipschitz norm bound and approximation independence of `SquareLpExtension`. -/
theorem stein_square_literal_fullLp {n : ℕ} (hn : 2 ≤ n) {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp2 : 2 ≤ p.toReal) {α : ℝ}
    (hα : max (1 / 2) ((n : ℝ) * (1 / 2 - 1 / p.toReal)) < α) :
    ∃ S : OAI.Analysis.Fourier.SquareFunction.SquareLpExtension n α p,
      ∀ f : SchwartzMap (Space n) ℂ,
        (fun x => ‖S.toFun (f.toLp p volume) x‖ₑ) =ᵐ[volume]
          OAI.Analysis.Fourier.SquareFunction.literalSteinSquareFunction α f := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨S⟩ := OAI.Analysis.Fourier.SquareFunction.stein_square_fullLp n hn p hp hp2 α hα
  exact ⟨S,fun f => S.schwartz_literal_enorm ((le_max_left _ _).trans_lt hα) f⟩

end OAI.Analysis.Fourier.SquareFunction
