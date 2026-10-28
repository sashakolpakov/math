import OAI.Analysis.PDE.Dirichlet.CalculusJointChartFields
import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.MooreResidual

noncomputable section
open Set Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion

variable {n : ℕ} {E X Z : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
local notation "V" => CoordinateSpace n 4

/-- Exact invariance of the physical Moore matrix under a nonlinear local
spatial chart, including the inverse-chart curvature. -/
theorem mooreChartMatrix_change_chart
    {u : E → ℝ} {G : X → E} {P : E → X} {x : X}
    (hu : ContDiffAt ℝ 2 u (G x)) (hG : ContDiffAt ℝ 2 G x)
    (hP : ContDiffAt ℝ 2 P (G x)) (hPG : P (G x) = x)
    (hGP : (fun y => G (P y)) =ᶠ[𝓝 (G x)] id)
    (Bg : V →L[ℝ] V →L[ℝ] ℝ) (J : V →L[ℝ] E) (K : V →L[ℝ] V →L[ℝ] E) :
    mooreChartMatrix Bg ((fderiv ℝ P (G x)).comp J)
      (composeChartCurvature (fderiv ℝ P (G x)) (fderiv ℝ (fderiv ℝ P) (G x)) J K)
      (fderiv ℝ (u ∘ G) x) (fderiv ℝ (fderiv ℝ (u ∘ G)) x) =
    mooreChartMatrix Bg J K (fderiv ℝ u (G x)) (fderiv ℝ (fderiv ℝ u) (G x)) := by
  unfold mooreChartMatrix
  congr 1
  funext i j
  exact congrArg (fun t => Bg (coordinateVector i) (coordinateVector j) + t)
    (scalar_secondJet_chart_identity hu hG hP hPG hGP J K
      (coordinateVector i) (coordinateVector j))

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
theorem mooreChartMatrix_jointChart
    (Bg : Z × E → V →L[ℝ] V →L[ℝ] ℝ) (J : Z × E → V →L[ℝ] E)
    (K : Z × E → V →L[ℝ] V →L[ℝ] E)
    {u : E → ℝ} {G : X → E} {P : E → X} {q : Z × X}
    (hu : ContDiffAt ℝ 2 u (G q.2)) (hG : ContDiffAt ℝ 2 G q.2)
    (hP : ContDiffAt ℝ 2 P (G q.2)) (hPG : P (G q.2) = q.2)
    (hGP : (fun y => G (P y)) =ᶠ[𝓝 (G q.2)] id) :
    mooreChartMatrix (jointChartBackground G Bg q) (jointChartJacobian P G J q)
      (jointChartCurvature P G J K q) (fderiv ℝ (u ∘ G) q.2)
      (fderiv ℝ (fderiv ℝ (u ∘ G)) q.2) =
    mooreChartMatrix (Bg (q.1,G q.2)) (J (q.1,G q.2)) (K (q.1,G q.2))
      (fderiv ℝ u (G q.2)) (fderiv ℝ (fderiv ℝ u) (G q.2)) :=
  mooreChartMatrix_change_chart hu hG hP hPG hGP _ _ _

end OAI.Analysis.PDE.Dirichlet
