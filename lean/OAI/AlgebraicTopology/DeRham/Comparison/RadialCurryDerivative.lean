import OAI.AlgebraicTopology.DeRham.Comparison.RadialOne
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Radial Curry Derivative -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.RadialCurryDerivative

noncomputable section

/-!
# Differentiating the actual radial homotopy integrand

This computes the derivative in the spatial variable of the integrand used by
`radialHomotopy`. It is a chain rule and evaluation rule for the genuine
continuous alternating maps; no homotopy or Poincare identity is assumed.
-/

set_option backward.isDefEq.respectTransparency false

open _root_.ContinuousAlternatingMap

attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup
  AddCommGroup.toAddCommMonoid NormedAddCommGroup.toSeminormedAddCommGroup
  NormedSpace.toModule

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {n : ℕ}

local instance radialCurryAuxAltSuccNormedGroup :
    NormedAddCommGroup (E [⋀^Fin (n + 1)]→L[ℝ] F) := inferInstance
local instance radialCurryAuxAltSuccNormedSpace :
    NormedSpace ℝ (E [⋀^Fin (n + 1)]→L[ℝ] F) := inferInstance
local instance radialCurryAuxAltNormedGroup :
    NormedAddCommGroup (E [⋀^Fin n]→L[ℝ] F) := inferInstance
local instance radialCurryAuxAltNormedSpace :
    NormedSpace ℝ (E [⋀^Fin n]→L[ℝ] F) := inferInstance
local instance radialCurryAuxDerivativeNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E [⋀^Fin n]→L[ℝ] F) := inferInstance
local instance radialCurryAuxDerivativeNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E [⋀^Fin n]→L[ℝ] F) := inferInstance

/-- Spatial derivative of the radial integrand, including the derivative of
the radial vector inserted into the first alternating slot. -/
theorem hasFDerivAt_radialIntegrand_aux
    {form : E → E [⋀^Fin (n + 1)]→L[ℝ] F} {x : E} (t : ℝ)
    (hform : DifferentiableAt ℝ form (t • x)) :
    HasFDerivAt (fun y => RadialOne.radialIntegrand form y t)
      (t ^ n • ((form (t • x)).curryLeft +
        t • RadialOne.contractionDerivative (fderiv ℝ form (t • x)) x)) x := by
  have hLc : IsBoundedLinearMap ℝ
      (fun a : E [⋀^Fin (n + 1)]→L[ℝ] F => a.curryLeft) := {
    map_add := by intro a b; ext y v; rfl
    map_smul := by intro c a; ext y v; rfl
    bound := ⟨1, zero_lt_one, by intro a; simp⟩ }
  let L : (E [⋀^Fin (n + 1)]→L[ℝ] F) →L[ℝ]
      (E →L[ℝ] E [⋀^Fin n]→L[ℝ] F) := hLc.toContinuousLinearMap
  have hinner := hform.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul t)
  have hL : HasFDerivAt
      (fun a : E [⋀^Fin (n + 1)]→L[ℝ] F => a.curryLeft) L (form (t • x)) := by
    exact hLc.hasFDerivAt
  have hcurried := hL.comp x hinner
  have heval := hcurried.clm_apply (hasFDerivAt_id x)
  have hscaled := heval.const_smul (t ^ n)
  convert hscaled using 1 <;> first
  | rfl
  | (ext y v
     simp [L, RadialOne.contractionDerivative, ContinuousLinearMap.comp_apply,
       ContinuousAlternatingMap.curryLeft_apply_apply]
     rfl)

/-- The same computation stated using the actual Frechet derivative. -/
theorem fderiv_radialIntegrand_aux
    {form : E → E [⋀^Fin (n + 1)]→L[ℝ] F} {x : E} (t : ℝ)
    (hform : DifferentiableAt ℝ form (t • x)) :
    fderiv ℝ (fun y => RadialOne.radialIntegrand form y t) x =
      t ^ n • ((form (t • x)).curryLeft +
        t • RadialOne.contractionDerivative (fderiv ℝ form (t • x)) x) :=
  (hasFDerivAt_radialIntegrand_aux t hform).fderiv

end

end OAI.AlgebraicTopology.DeRham.Comparison.RadialCurryDerivative
