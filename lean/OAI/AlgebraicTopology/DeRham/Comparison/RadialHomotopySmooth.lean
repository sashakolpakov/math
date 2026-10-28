import OAI.AlgebraicTopology.DeRham.Comparison.ParameterIntegralSmooth
import OAI.AlgebraicTopology.DeRham.Comparison.RadialExteriorIntegral

/-! # Radial Homotopy Smooth -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.RadialHomotopySmooth

noncomputable section

/-!
# Smoothness of the radial homotopy operator

The coefficient function of the actual radial homotopy integral is smooth.
-/

open scoped ContDiff

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

/-- The radial homotopy integral of a smooth differential form is smooth. -/
theorem contDiff_radialHomotopy
    {form : E → E [⋀^Fin (n + 1)]→L[ℝ] F} (hform : ContDiff ℝ ∞ form) :
    ContDiff ℝ ∞ (RadialOne.radialHomotopy form) :=
  ParameterIntegralSmooth.contDiff_intervalIntegral_of_smooth (RadialExteriorIntegral.contDiff_radialIntegrand hform) 0 1

end

end OAI.AlgebraicTopology.DeRham.Comparison.RadialHomotopySmooth
