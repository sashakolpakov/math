import OAI.Analysis.Calculus.SmoothExtension.Periodic.TangentChart

/-! Exact local conversion between twice differentiating in the extended
periodic tangent fields and the corresponding coordinate second derivative. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.Calculus.SmoothExtension

open OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem twice_fieldDerivative_eq_chart_second
    {G P : E → E} {u : E → ℝ} {T S : E → E}
    (hG : ContDiff ℝ 3 G) (hP : ContDiff ℝ 3 P) (hu : ContDiff ℝ 3 u)
    (v w z : E) (hinv : (fun y ↦ P (G y)) =ᶠ[𝓝 z] id)
    (hT : T =ᶠ[𝓝 (G z)] OAI.Analysis.PDE.Elliptic.chartTangentField G P v)
    (hS : S =ᶠ[𝓝 (G z)] OAI.Analysis.PDE.Elliptic.chartTangentField G P w) :
    OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative u T) S (G z) =
      fderiv ℝ (fderiv ℝ (fun y ↦ u (G y))) z w v := by
  have he : OAI.Analysis.PDE.Elliptic.fieldDerivative u T =ᶠ[𝓝 (G z)]
      OAI.Analysis.PDE.Elliptic.fieldDerivative u (OAI.Analysis.PDE.Elliptic.chartTangentField G P v) := by
    filter_upwards [hT] with y hy
    simp only [OAI.Analysis.PDE.Elliptic.fieldDerivative, hy]
  change fderiv ℝ (OAI.Analysis.PDE.Elliptic.fieldDerivative u T) (G z) (S (G z)) = _
  rw [he.fderiv_eq, hS.eq_of_nhds]
  simpa only [OAI.Analysis.PDE.Elliptic.chartFieldNormal, OAI.Analysis.PDE.Elliptic.chartTangentField, hinv.eq_of_nhds, id_eq] using
    OAI.Analysis.PDE.Elliptic.chart_field_normal_eq hG hP hu v w z hinv

omit [FiniteDimensional ℝ E] in
theorem twice_fieldDerivative_chart_germ
    {G P : E → E} {u : E → ℝ} {T S : E → E}
    (hG : ContDiff ℝ 3 G) (hP : ContDiff ℝ 3 P) (hu : ContDiff ℝ 3 u)
    (v w z : E) (hinv : (fun y ↦ P (G y)) =ᶠ[𝓝 z] id)
    (hT : T =ᶠ[𝓝 (G z)] OAI.Analysis.PDE.Elliptic.chartTangentField G P v)
    (hS : S =ᶠ[𝓝 (G z)] OAI.Analysis.PDE.Elliptic.chartTangentField G P w) :
    (fun y ↦ OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative u T) S (G y)) =ᶠ[𝓝 z]
      (fun y ↦ fderiv ℝ (fderiv ℝ (fun x ↦ u (G x))) y w v) := by
  have hTn := (hG.continuous.tendsto z).eventually hT.eventuallyEq_nhds
  have hSn := (hG.continuous.tendsto z).eventually hS.eventuallyEq_nhds
  filter_upwards [hinv.eventuallyEq_nhds, hTn, hSn] with y hy hTy hSy
  exact twice_fieldDerivative_eq_chart_second hG hP hu v w y hy hTy hSy

end OAI.Analysis.Calculus.SmoothExtension
