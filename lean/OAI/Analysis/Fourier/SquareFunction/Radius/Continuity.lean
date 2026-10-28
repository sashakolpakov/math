import OAI.Analysis.Fourier.SquareFunction.Radius.ContinuityCore
import OAI.Analysis.Fourier.SquareFunction.Radius.Integrable

open OAI.Analysis.Fourier.Wave

noncomputable section
open Set _root_.MeasureTheory

namespace OAI.Analysis.Fourier.SquareFunction

/-- Continuity at every positive radius, including radii whose multiplier
has an integrable sphere singularity. Scaling reduces the assertion to a
single fixed integrable weight and dominated convergence. -/
theorem continuousOn_radius_derivative_integral {n : ℕ} [NeZero n] {α : ℝ}
    (hα : 1 / 2 < α) {g : Space n → ℂ} (hg : Continuous g)
    {M : ℝ} (hM : ∀ ξ, ‖g ξ‖ ≤ M) :
    ContinuousOn (fun r => ∫ ξ, (r⁻¹ * radiusMultiplier α ‖ξ‖ r) • g ξ) (Ioi 0) :=
  continuousOn_radius_derivative_integral_of_unit_integrable α
    (integrable_radiusMultiplier_unit hα) hg hM

end OAI.Analysis.Fourier.SquareFunction
