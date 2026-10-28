import OAI.Analysis.PDE.Dirichlet.CalculusJointChartAlgebra

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

variable {V E X Z : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Pullback of an inverse Jacobian to a fixed spatial chart. -/
def jointChartJacobian (P : E → X) (G : X → E) (J : Z × E → V →L[ℝ] E)
    (q : Z × X) : V →L[ℝ] X :=
  (fderiv ℝ P (G q.2)).comp (J (q.1,G q.2))

/-- Pullback of an inverse Hessian to a fixed spatial chart. -/
def jointChartCurvature (P : E → X) (G : X → E)
    (J : Z × E → V →L[ℝ] E) (K : Z × E → V →L[ℝ] V →L[ℝ] E)
    (q : Z × X) : V →L[ℝ] V →L[ℝ] X :=
  composeChartCurvature (fderiv ℝ P (G q.2)) (fderiv ℝ (fderiv ℝ P) (G q.2))
    (J (q.1,G q.2)) (K (q.1,G q.2))

def jointChartBackground (G : X → E) (Bg : Z × E → V →L[ℝ] V →L[ℝ] ℝ)
    (q : Z × X) : V →L[ℝ] V →L[ℝ] ℝ := Bg (q.1,G q.2)

def jointChartLoad (G : X → E) (load : Z × E → ℝ) (q : Z × X) : ℝ :=
  load (q.1,G q.2)

theorem contDiff_jointChartJacobian {P : E → X} {G : X → E}
    {J : Z × E → V →L[ℝ] E}
    (hP : ContDiff ℝ ∞ P) (hG : ContDiff ℝ ∞ G) (hJ : ContDiff ℝ ∞ J) :
    ContDiff ℝ ∞ (jointChartJacobian P G J) := by
  have hg : ContDiff ℝ ∞ (fun q : Z × X => G q.2) := hG.comp contDiff_snd
  have hA := (hP.fderiv_right (m := ∞) (by simp)).comp hg
  have hJ' := hJ.comp (contDiff_fst.prodMk hg)
  exact hA.clm_comp hJ'

theorem contDiff_jointChartCurvature {P : E → X} {G : X → E}
    {J : Z × E → V →L[ℝ] E} {K : Z × E → V →L[ℝ] V →L[ℝ] E}
    (hP : ContDiff ℝ ∞ P) (hG : ContDiff ℝ ∞ G)
    (hJ : ContDiff ℝ ∞ J) (hK : ContDiff ℝ ∞ K) :
    ContDiff ℝ ∞ (jointChartCurvature P G J K) := by
  have hD := hP.fderiv_right (m := ∞) (by simp)
  have hDD := hD.fderiv_right (m := ∞) (by simp)
  have hg : ContDiff ℝ ∞ (fun q : Z × X => G q.2) := hG.comp contDiff_snd
  have hq : ContDiff ℝ ∞ (fun q : Z × X => (q.1,G q.2)) := contDiff_fst.prodMk hg
  exact contDiff_composeChartCurvature (hD.comp hg) (hDD.comp hg)
    (hJ.comp hq) (hK.comp hq)

theorem contDiff_jointChartBackground {G : X → E}
    {Bg : Z × E → V →L[ℝ] V →L[ℝ] ℝ}
    (hG : ContDiff ℝ ∞ G) (hBg : ContDiff ℝ ∞ Bg) :
    ContDiff ℝ ∞ (jointChartBackground G Bg) :=
  hBg.comp (contDiff_fst.prodMk (hG.comp contDiff_snd))

theorem contDiff_jointChartLoad {G : X → E} {load : Z × E → ℝ}
    (hG : ContDiff ℝ ∞ G) (hl : ContDiff ℝ ∞ load) :
    ContDiff ℝ ∞ (jointChartLoad G load) :=
  hl.comp (contDiff_fst.prodMk (hG.comp contDiff_snd))

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
theorem jointChartJacobian_surjective {P : E → X} {G : X → E}
    (J : Z × E → V →L[ℝ] E) {q : Z × X}
    (hG : DifferentiableAt ℝ G q.2) (hP : DifferentiableAt ℝ P (G q.2))
    (hi : (fun y => P (G y)) =ᶠ[𝓝 q.2] id)
    (hJ : Function.Surjective (J (q.1,G q.2))) :
    Function.Surjective (jointChartJacobian P G J q) :=
  chart_jacobian_surjective hG hP hi _ hJ

end OAI.Analysis.PDE.Dirichlet
