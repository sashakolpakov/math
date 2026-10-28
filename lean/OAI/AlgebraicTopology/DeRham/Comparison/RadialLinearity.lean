import OAI.AlgebraicTopology.DeRham.Comparison.RadialOne
import Mathlib.Analysis.Complex.Basic

/-! # Radial Linearity -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.RadialLinearity

noncomputable section

/-! # Linearity of the actual radial homotopy operator -/

open _root_.MeasureTheory _root_.ContinuousAlternatingMap

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n : ℕ}

theorem radialIntegrand_add
    (form other : E → E [⋀^Fin (n + 1)]→L[ℝ] F) (x : E) (t : ℝ) :
    RadialOne.radialIntegrand (form + other) x t =
      RadialOne.radialIntegrand form x t + RadialOne.radialIntegrand other x t := by
  simp [RadialOne.radialIntegrand, Pi.add_apply, smul_add]

theorem radialHomotopy_add
    {form other : E → E [⋀^Fin (n + 1)]→L[ℝ] F}
    (hform : Continuous form) (hother : Continuous other) (x : E) :
    RadialOne.radialHomotopy (form + other) x = RadialOne.radialHomotopy form x + RadialOne.radialHomotopy other x := by
  simp only [RadialOne.radialHomotopy, radialIntegrand_add]
  exact intervalIntegral.integral_add (RadialOne.intervalIntegrable_radialIntegrand hform x)
    (RadialOne.intervalIntegrable_radialIntegrand hother x)

theorem radialIntegrand_complex_smul
    (c : ℂ) (form : E → E [⋀^Fin (n + 1)]→L[ℝ] ℂ) (x : E) (t : ℝ) :
    RadialOne.radialIntegrand (c • form) x t = c • RadialOne.radialIntegrand form x t := by
  ext v
  change (t ^ n : ℝ) • (c • form (t • x) (Matrix.vecCons x v)) =
    c • ((t ^ n : ℝ) • form (t • x) (Matrix.vecCons x v))
  exact smul_comm _ _ _

theorem radialHomotopy_complex_smul
    (c : ℂ) (form : E → E [⋀^Fin (n + 1)]→L[ℝ] ℂ) (x : E) :
    RadialOne.radialHomotopy (c • form) x = c • RadialOne.radialHomotopy form x := by
  simp only [RadialOne.radialHomotopy, radialIntegrand_complex_smul]
  exact intervalIntegral.integral_smul c _

end

end OAI.AlgebraicTopology.DeRham.Comparison.RadialLinearity
