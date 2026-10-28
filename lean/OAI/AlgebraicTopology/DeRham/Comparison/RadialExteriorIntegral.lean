import OAI.AlgebraicTopology.DeRham.Comparison.ParameterIntegralDerivative
import OAI.AlgebraicTopology.DeRham.Comparison.RadialOne
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Radial Exterior Integral -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.RadialExteriorIntegral

noncomputable section

section

/-!
# Differentiation of the actual radial homotopy integral

This applies parameter differentiation to the concrete radial integrand.
-/

set_option backward.isDefEq.respectTransparency false

open _root_.MeasureTheory _root_.ContinuousAlternatingMap
open scoped ContDiff

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {n : ℕ} {r : ℕ∞ω}

-- Select the operator-norm instances explicitly. The generic topological
-- instances on continuous alternating maps otherwise compete during elaboration.
local instance : NormedAddCommGroup (E [⋀^Fin n]→L[ℝ] F) := inferInstance
local instance : NormedSpace ℝ (E [⋀^Fin n]→L[ℝ] F) := inferInstance
local instance : NormedAddCommGroup (E →L[ℝ] (E [⋀^Fin n]→L[ℝ] F)) := inferInstance

/-- The radial integrand has the same joint smoothness as the form. -/
theorem contDiff_radialIntegrand
    {form : E → E [⋀^Fin (n + 1)]→L[ℝ] F} (hform : ContDiff ℝ r form) :
    ContDiff ℝ r (fun z : E × ℝ => RadialOne.radialIntegrand form z.1 z.2) := by
  have hdilate : ContDiff ℝ r (fun z : E × ℝ => z.2 • z.1) :=
    contDiff_snd.smul contDiff_fst
  have hlinear : ContDiff ℝ r (fun α : E [⋀^Fin (n + 1)]→L[ℝ] F => α.curryLeft) := by
    have h := LinearIsometry.contDiff (n := r)
      (curryLeftLI (𝕜 := ℝ) (E := E) (F := F) (n := n))
    convert h using 1
    ext α v w
    rfl
  have hcurry : ContDiff ℝ r (fun z : E × ℝ => (form (z.2 • z.1)).curryLeft) :=
    hlinear.comp (hform.comp hdilate)
  exact (contDiff_snd.pow n).smul (hcurry.clm_apply contDiff_fst)

/-- The parameter derivatives needed for the homotopy formula are genuinely integrable. -/
theorem intervalIntegrable_fderiv_radialIntegrand
    {form : E → E [⋀^Fin (n + 1)]→L[ℝ] F} (hform : ContDiff ℝ 1 form) (x : E) :
    IntervalIntegrable (fun t => fderiv ℝ (fun y => RadialOne.radialIntegrand form y t) x)
      volume 0 1 :=
  ParameterIntegralDerivative.intervalIntegrable_parameterFDeriv (contDiff_radialIntegrand hform) x 0 1

variable [FiniteDimensional ℝ E]

/-- Differentiate the radial homotopy by integrating the parameter derivative
of its concrete integrand. -/
theorem hasFDerivAt_radialHomotopy
    {form : E → E [⋀^Fin (n + 1)]→L[ℝ] F} (hform : ContDiff ℝ 1 form) (x : E) :
    HasFDerivAt (RadialOne.radialHomotopy form)
      (∫ t in (0 : ℝ)..1, fderiv ℝ (fun y => RadialOne.radialIntegrand form y t) x) x :=
  ParameterIntegralDerivative.hasFDerivAt_intervalIntegral_of_contDiff (contDiff_radialIntegrand hform) x 0 1

/-- The corresponding equality of actual Fréchet derivatives. -/
theorem fderiv_radialHomotopy
    {form : E → E [⋀^Fin (n + 1)]→L[ℝ] F} (hform : ContDiff ℝ 1 form) (x : E) :
    fderiv ℝ (RadialOne.radialHomotopy form) x =
      ∫ t in (0 : ℝ)..1, fderiv ℝ (fun y => RadialOne.radialIntegrand form y t) x :=
  (hasFDerivAt_radialHomotopy hform x).fderiv

end

/-! # Exterior differentiation of the actual radial integral -/

set_option backward.isDefEq.respectTransparency false

open _root_.MeasureTheory _root_.ContinuousAlternatingMap
open scoped Interval

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {n : ℕ}

local instance exteriorIntegralAltNormedGroup :
    NormedAddCommGroup (E [⋀^Fin n]→L[ℝ] F) := inferInstance
local instance exteriorIntegralAltNormedSpace :
    NormedSpace ℝ (E [⋀^Fin n]→L[ℝ] F) := inferInstance
local instance exteriorIntegralClmNormedGroup :
    NormedAddCommGroup (E →L[ℝ] (E [⋀^Fin n]→L[ℝ] F)) := inferInstance

/-- Exterior differentiation commutes with the concrete radial parameter
integral in a finite-dimensional chart. -/
theorem extDeriv_radialHomotopy_eq_integral
    {form : E → E [⋀^Fin (n + 1)]→L[ℝ] F} (hform : ContDiff ℝ 1 form) (x : E) :
    extDeriv (RadialOne.radialHomotopy form) x =
      ∫ t in (0 : ℝ)..1, extDeriv (fun y ↦ RadialOne.radialIntegrand form y t) x := by
  unfold extDeriv
  rw [fderiv_radialHomotopy hform x]
  exact ((alternatizeUncurryFinCLM ℝ E F).intervalIntegral_comp_comm
    (intervalIntegrable_fderiv_radialIntegrand hform x)).symm

end

end OAI.AlgebraicTopology.DeRham.Comparison.RadialExteriorIntegral
