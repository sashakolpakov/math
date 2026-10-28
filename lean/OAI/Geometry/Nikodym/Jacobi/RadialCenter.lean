import OAI.Geometry.Nikodym.Jacobi.ExponentialFormula
import OAI.Geometry.Nikodym.Jacobi.RadialMap

noncomputable section
namespace OAI.Geometry.Nikodym

open Set Filter Metric
open scoped RealInnerProductSpace Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem projectiveRadialMap_eq_exponential (κ : ℝ) (x : E) :
    projectiveRadialMap κ x = (radialExponential κ x).1⁻¹ • (radialExponential κ x).2 := by
  rw [radialExponential_formula]
  simp only [projectiveRadialMap,curvatureTan,smul_smul]
  congr 1
  ring

omit [FiniteDimensional ℝ E] in
@[simp] theorem projectiveRadialMap_zero (κ : ℝ) : projectiveRadialMap κ (0:E) = 0 := by
  simp [projectiveRadialMap]

/-- The apparent radial singularity at the center is removable to every
order, by the smooth operator-exponential formula. -/
theorem contDiffAt_projectiveRadialMap_center_included (κ : ℝ) {x : E}
    (hc : curvatureCos κ ‖x‖ ≠ 0) : ContDiffAt ℝ ∞ (projectiveRadialMap κ) x := by
  have he : (radialExponential κ x).1 ≠ 0 := by rwa [radialExponential_formula]
  have hf := ((contDiff_radialExponential (E := E) κ).fst.contDiffAt.inv he).smul
    (contDiff_radialExponential (E := E) κ).snd.contDiffAt
  change ContDiffAt ℝ ∞ (fun y : E =>
    (radialExponential κ y).1⁻¹ • (radialExponential κ y).2) x at hf
  have hfun : projectiveRadialMap κ = fun y : E =>
      (radialExponential κ y).1⁻¹ • (radialExponential κ y).2 :=
    funext (projectiveRadialMap_eq_exponential κ)
  rwa [← hfun] at hf

theorem hasFDerivAt_projectiveRadialMap_zero (κ : ℝ) :
    HasFDerivAt (projectiveRadialMap κ : E → E) (ContinuousLinearMap.id ℝ E) 0 := by
  have ha := (hasFDerivAt_radialExponential_zero (E := E) κ).fst
  have hb := (hasFDerivAt_radialExponential_zero (E := E) κ).snd
  have hi := (hasDerivAt_inv (by simp : (radialExponential κ (0:E)).1 ≠ 0)).comp_hasFDerivAt (0:E) ha
  have hd := hi.smul hb
  convert hd using 1
  · exact funext (projectiveRadialMap_eq_exponential κ)
  · ext x
    simp

theorem projectiveRadialMap_pullback_metric_zero (κ : ℝ) (w z : E) :
    beltramiMetric κ (projectiveRadialMap κ (0:E))
      (fderiv ℝ (projectiveRadialMap κ) 0 w)
      (fderiv ℝ (projectiveRadialMap κ) 0 z) = inner ℝ w z := by
  rw [projectiveRadialMap_zero,(hasFDerivAt_projectiveRadialMap_zero κ).fderiv]
  simp [beltramiMetric,beltramiDenominator]

end OAI.Geometry.Nikodym
