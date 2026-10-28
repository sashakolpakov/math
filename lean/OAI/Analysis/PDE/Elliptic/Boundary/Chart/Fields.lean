import OAI.Analysis.PDE.Elliptic.Boundary.LogRemainderHolder
import OAI.Analysis.PDE.Elliptic.Boundary.NormalizedChart

/-! Coordinate tangent fields are pushed forward by the genuine boundary chart.
Their differentiated scalar fields are exactly mixed derivatives in flat coordinates. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Filter InnerProductSpace
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def chartTangentField (F P : E → E) (e y : E) : E := fderiv ℝ F (P y) e

omit [FiniteDimensional ℝ E] in
theorem contDiff_chartTangentField {F P : E → E}
    (hF : ContDiff ℝ 3 F) (hP : ContDiff ℝ 3 P) (e : E) :
    ContDiff ℝ 2 (chartTangentField F P e) := by
  have hDF : ContDiff ℝ 2 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  exact (hDF.comp (hP.of_le (by norm_num))).clm_apply contDiff_const

omit [FiniteDimensional ℝ E] in
theorem chart_field_comp {F P : E → E} {u : E → ℝ}
    (hF : Differentiable ℝ F) (hu : Differentiable ℝ u) (e z : E)
    (hinv : P (F z) = z) :
    fieldDerivative u (chartTangentField F P e) (F z) =
      fderiv ℝ (fun y => u (F y)) z e := by
  rw [show fderiv ℝ (fun y => u (F y)) z =
      (fderiv ℝ u (F z)).comp (fderiv ℝ F z) from
      ((hu (F z)).hasFDerivAt.comp z (hF z).hasFDerivAt).fderiv]
  simp only [fieldDerivative, chartTangentField, hinv, ContinuousLinearMap.comp_apply]

omit [FiniteDimensional ℝ E] in
theorem chart_field_normal_eq {F P : E → E} {u : E → ℝ}
    (hF : ContDiff ℝ 3 F) (hP : ContDiff ℝ 3 P) (hu : ContDiff ℝ 3 u)
    (e v z : E) (hinv : (fun y => P (F y)) =ᶠ[𝓝 z] id) :
    chartFieldNormal u (chartTangentField F P e) F v z =
      fderiv ℝ (fderiv ℝ (fun y => u (F y))) z v e := by
  have hT := contDiff_chartTangentField hF hP e
  have hW : ContDiff ℝ 2 (fieldDerivative u (chartTangentField F P e)) :=
    contDiff_fieldDerivative hu hT (by norm_num)
  have hcomp : (fun y => fieldDerivative u (chartTangentField F P e) (F y)) =ᶠ[𝓝 z]
      (fun y => fderiv ℝ (fun q => u (F q)) y e) := by
    filter_upwards [hinv] with y hy
    exact chart_field_comp (hF.differentiable (by norm_num))
      (hu.differentiable (by norm_num)) e y hy
  have hder := hcomp.fderiv_eq (𝕜 := ℝ)
  have hl : fderiv ℝ (fun y => fieldDerivative u (chartTangentField F P e) (F y)) z =
      (fderiv ℝ (fieldDerivative u (chartTangentField F P e)) (F z)).comp (fderiv ℝ F z) :=
    ((hW.differentiable (by norm_num) (F z)).hasFDerivAt.comp z
      (hF.differentiable (by norm_num) z).hasFDerivAt).fderiv
  have hUF : ContDiff ℝ 3 (fun y => u (F y)) := hu.comp hF
  have hDUF : ContDiff ℝ 2 (fderiv ℝ (fun y => u (F y))) := hUF.fderiv_right (by norm_num)
  have hr := ((hDUF.differentiable (by norm_num) z).hasFDerivAt.clm_apply
    (hasFDerivAt_const e z)).fderiv
  rw [hl, hr] at hder
  have hh := congrArg (fun L : E →L[ℝ] ℝ => L v) hder
  simpa [chartFieldNormal] using hh

end OAI.Analysis.PDE.Elliptic
