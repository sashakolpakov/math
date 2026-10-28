import OAI.Analysis.PDE.Elliptic.Boundary.ChainRule

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

local instance jointChartMapGroup (A B : Type*) [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] : NormedAddCommGroup (A →L[ℝ] B) := inferInstance
local instance jointChartMapSpace (A B : Type*) [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] : NormedSpace ℝ (A →L[ℝ] B) := inferInstance

variable {V E X Z : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Curvature of a composite inverse map, allowing distinct physical,
reference, and chart spaces. -/
def composeChartCurvature (A : E →L[ℝ] X) (B : E →L[ℝ] E →L[ℝ] X)
    (J : V →L[ℝ] E) (K : V →L[ℝ] V →L[ℝ] E) : V →L[ℝ] V →L[ℝ] X :=
  ((ContinuousLinearMap.compL ℝ V E X).flip J).comp (B.comp J) +
    ((ContinuousLinearMap.compL ℝ V E X) A).comp K

@[simp] theorem composeChartCurvature_apply
    (A : E →L[ℝ] X) (B : E →L[ℝ] E →L[ℝ] X)
    (J : V →L[ℝ] E) (K : V →L[ℝ] V →L[ℝ] E) (v w : V) :
    composeChartCurvature A B J K v w = B (J v) (J w) + A (K v w) := rfl

theorem contDiffOn_composeChartCurvature {S : Set Z} {q : ℕ∞ω}
    {A : Z → E →L[ℝ] X} {B : Z → E →L[ℝ] E →L[ℝ] X}
    {J : Z → V →L[ℝ] E} {K : Z → V →L[ℝ] V →L[ℝ] E}
    (hA : ContDiffOn ℝ q A S) (hB : ContDiffOn ℝ q B S)
    (hJ : ContDiffOn ℝ q J S) (hK : ContDiffOn ℝ q K S) :
    ContDiffOn ℝ q (fun z => composeChartCurvature (A z) (B z) (J z) (K z)) S := by
  have hl := (ContinuousLinearMap.compL ℝ V E X).flip.contDiff.comp_contDiffOn hJ
  have hr := hB.clm_comp hJ
  have hp := (ContinuousLinearMap.compL ℝ V E X).contDiff.comp_contDiffOn hA
  exact (hl.clm_comp hr).add (hp.clm_comp hK)

theorem contDiff_composeChartCurvature {q : ℕ∞ω}
    {A : Z → E →L[ℝ] X} {B : Z → E →L[ℝ] E →L[ℝ] X}
    {J : Z → V →L[ℝ] E} {K : Z → V →L[ℝ] V →L[ℝ] E}
    (hA : ContDiff ℝ q A) (hB : ContDiff ℝ q B)
    (hJ : ContDiff ℝ q J) (hK : ContDiff ℝ q K) :
    ContDiff ℝ q (fun z => composeChartCurvature (A z) (B z) (J z) (K z)) := by
  exact contDiffOn_univ.mp (contDiffOn_composeChartCurvature
    hA.contDiffOn hB.contDiffOn hJ.contDiffOn hK.contDiffOn)

/-- Both differentiated identities of a genuine local change of coordinates. -/
theorem scalar_jets_of_chart_inverse
    {u : E → ℝ} {G : X → E} {P : E → X} {x : X}
    (hu : ContDiffAt ℝ 2 u (G x)) (hG : ContDiffAt ℝ 2 G x)
    (hP : ContDiffAt ℝ 2 P (G x)) (hPG : P (G x) = x)
    (hGP : (fun y => G (P y)) =ᶠ[𝓝 (G x)] id) :
    (fderiv ℝ (u ∘ G) x).comp (fderiv ℝ P (G x)) = fderiv ℝ u (G x) ∧
    ∀ v w : E,
      fderiv ℝ (fderiv ℝ (u ∘ G)) x
          (fderiv ℝ P (G x) v) (fderiv ℝ P (G x) w) +
        fderiv ℝ (u ∘ G) x (fderiv ℝ (fderiv ℝ P) (G x) v w) =
      fderiv ℝ (fderiv ℝ u) (G x) v w := by
  have hf : ContDiffAt ℝ 2 (u ∘ G) (P (G x)) := by
    rw [hPG]
    exact hu.comp x hG
  have he : (fun y => (u ∘ G) (P y)) =ᶠ[𝓝 (G x)] u := by
    filter_upwards [hGP] with y hy
    change u (G (P y)) = u y
    rw [hy]
    rfl
  constructor
  · have hd := fderiv_fun_comp (G x) (hf.differentiableAt (by norm_num))
      (hP.differentiableAt (by norm_num))
    rw [hPG] at hd
    exact hd.symm.trans he.fderiv_eq
  · intro v w
    have hdd := OAI.Analysis.PDE.Elliptic.second_fderiv_comp hf hP v w
    rw [hPG] at hdd
    exact hdd.symm.trans (congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L v w)
      (he.fderiv.fderiv_eq))

/-- The full scalar Hessian expression is unchanged by passing to a local
chart; this includes the curvature term, not just a linear congruence. -/
theorem scalar_secondJet_chart_identity
    {u : E → ℝ} {G : X → E} {P : E → X} {x : X}
    (hu : ContDiffAt ℝ 2 u (G x)) (hG : ContDiffAt ℝ 2 G x)
    (hP : ContDiffAt ℝ 2 P (G x)) (hPG : P (G x) = x)
    (hGP : (fun y => G (P y)) =ᶠ[𝓝 (G x)] id)
    (J : V →L[ℝ] E) (K : V →L[ℝ] V →L[ℝ] E) (v w : V) :
    fderiv ℝ (fderiv ℝ (u ∘ G)) x
        (((fderiv ℝ P (G x)).comp J) v) (((fderiv ℝ P (G x)).comp J) w) +
      fderiv ℝ (u ∘ G) x
        (composeChartCurvature (fderiv ℝ P (G x))
          (fderiv ℝ (fderiv ℝ P) (G x)) J K v w) =
    fderiv ℝ (fderiv ℝ u) (G x) (J v) (J w) + fderiv ℝ u (G x) (K v w) := by
  obtain ⟨hfirst,hsecond⟩ := scalar_jets_of_chart_inverse hu hG hP hPG hGP
  simp only [composeChartCurvature_apply, ContinuousLinearMap.comp_apply, map_add]
  rw [← add_assoc, hsecond]
  exact congrArg (fun t => fderiv ℝ (fderiv ℝ u) (G x) (J v) (J w) + t)
    (congrArg (fun L : E →L[ℝ] ℝ => L (K v w)) hfirst)

theorem chart_jacobian_surjective
    {G : X → E} {P : E → X} {x : X}
    (hG : DifferentiableAt ℝ G x) (hP : DifferentiableAt ℝ P (G x))
    (hPG : (fun y => P (G y)) =ᶠ[𝓝 x] id)
    (J : V →L[ℝ] E) (hJ : Function.Surjective J) :
    Function.Surjective ((fderiv ℝ P (G x)).comp J) := by
  have he : (fderiv ℝ P (G x)).comp (fderiv ℝ G x) = ContinuousLinearMap.id ℝ X := by
    rw [← fderiv_comp x hP hG]
    simpa only [Function.comp_def, fderiv_id] using hPG.fderiv_eq (𝕜 := ℝ)
  intro y
  obtain ⟨v,hv⟩ := hJ (fderiv ℝ G x y)
  refine ⟨v,?_⟩
  change fderiv ℝ P (G x) (J v) = y
  rw [hv]
  exact congrArg (fun L : X →L[ℝ] X => L y) he

end OAI.Analysis.PDE.Dirichlet
