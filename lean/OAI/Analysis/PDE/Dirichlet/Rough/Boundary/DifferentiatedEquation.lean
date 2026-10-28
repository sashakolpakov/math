import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.NormalClosedJet

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance linearizedFirstGroup (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    NormedAddCommGroup (V →L[ℝ] ℝ) := inferInstance
local instance linearizedFirstSpace (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    NormedSpace ℝ (V →L[ℝ] ℝ) := inferInstance
local instance linearizedSecondGroup (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
local instance linearizedSecondSpace (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
local instance linearizedThirdGroup (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    NormedAddCommGroup (V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
local instance linearizedThirdSpace (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    NormedSpace ℝ (V →L[ℝ] V →L[ℝ] V →L[ℝ] ℝ) := inferInstance

abbrev NonlinearJet (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (E × (E →L[ℝ] ℝ)) × (E →L[ℝ] E →L[ℝ] ℝ)

def nonlinearTwoJet (f : E → ℝ) (x : E) : NonlinearJet E :=
  ((x,fderiv ℝ f x),fderiv ℝ (fderiv ℝ f) x)

theorem fderiv_constantDirectional_eq {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (v : E) :
    fderiv ℝ (constantDirectional f v) x = fderiv ℝ (fderiv ℝ f) x v := by
  ext w
  rw [fderiv_constantDirectional_apply hf, (hf.isSymmSndFDerivAt (by norm_num)).eq]

theorem hessian_constantDirectional_eq {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 3 f x) (v : E) :
    fderiv ℝ (fderiv ℝ (constantDirectional f v)) x =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x v := by
  have he : fderiv ℝ (constantDirectional f v) =ᶠ[𝓝 x]
      fun y ↦ fderiv ℝ (fderiv ℝ f) y v := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact fderiv_constantDirectional_eq (hy.of_le (by norm_num)) v
  rw [he.fderiv_eq]
  have hH := ((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right
    (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hder := ((ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) v).hasFDerivAt.comp x hH.hasFDerivAt).fderiv
  change fderiv ℝ (fun y ↦ fderiv ℝ (fderiv ℝ f) y v) x = _ at hder
  rw [hder]
  ext w z
  exact congrArg (fun L : E →L[ℝ] ℝ ↦ L z)
    (((hf.fderiv_right (m := 2) (by norm_num)).isSymmSndFDerivAt (by norm_num)).eq w v)

theorem contDiff_nonlinearTwoJet {f : E → ℝ} {k : ℕ} (hf : ContDiff ℝ (k+2) f) :
    ContDiff ℝ k (nonlinearTwoJet f) := by
  exact (contDiff_id.prodMk (hf.fderiv_right (m := k) (by exact_mod_cast (by omega : k+1 ≤ k+2)))).prodMk
    ((hf.fderiv_right (m := k+1) (by norm_cast)).fderiv_right (m := k) (by norm_cast))

theorem fderiv_nonlinearTwoJet_apply {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 3 f x) (v : E) :
    fderiv ℝ (nonlinearTwoJet f) x v =
      ((v,fderiv ℝ (constantDirectional f v) x),
        fderiv ℝ (fderiv ℝ (constantDirectional f v)) x) := by
  have hD := (hf.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have hH := ((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right
    (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he := (((hasFDerivAt_id x).prodMk hD.hasFDerivAt).prodMk hH.hasFDerivAt).fderiv
  simp only [id_eq] at he
  change fderiv ℝ (fun y ↦ ((y,fderiv ℝ f y),fderiv ℝ (fderiv ℝ f) y)) x v = _
  rw [he, fderiv_constantDirectional_eq (hf.of_le (by norm_num)), hessian_constantDirectional_eq hf]
  rfl

def differentiatedResidual (F : NonlinearJet E → ℝ) (f : E → ℝ) (v : E)
    (p : NonlinearJet E) : ℝ :=
  fderiv ℝ F (nonlinearTwoJet f p.1.1) ((v,p.1.2),p.2)

theorem contDiff_differentiatedResidual {F : NonlinearJet E → ℝ} {f : E → ℝ}
    (hF : ContDiff ℝ 2 F) (hf : ContDiff ℝ 3 f) (v : E) :
    ContDiff ℝ 1 (differentiatedResidual F f v) := by
  have hJ : ContDiff ℝ 1 (nonlinearTwoJet f) := contDiff_nonlinearTwoJet hf
  exact ((hF.fderiv_right (m := 1) (by norm_num)).comp
    (hJ.comp contDiff_fst.fst)).clm_apply
      ((contDiff_const.prodMk contDiff_fst.snd).prodMk contDiff_snd)

/-- Differentiating the actual equation, including at boundary points by
uniqueness of the closed-set derivative, gives the linearized equation. -/
theorem differentiatedResidual_equation {F : NonlinearJet E → ℝ} {f : E → ℝ}
    (hF : ContDiff ℝ 2 F) (hf : ContDiff ℝ 3 f)
    {S : Set E} (hS : UniqueDiffOn ℝ S)
    (he : ∀ x ∈ S, F (nonlinearTwoJet f x) = 0)
    (v : E) {x : E} (hx : x ∈ S) :
    differentiatedResidual F f v (nonlinearTwoJet (constantDirectional f v) x) = 0 := by
  have hJ : DifferentiableAt ℝ (nonlinearTwoJet f) x :=
    (contDiff_nonlinearTwoJet (k := 1) hf).differentiable (by norm_num) x
  have hd := (hF.differentiable (by norm_num) (nonlinearTwoJet f x)).hasFDerivAt.comp x hJ.hasFDerivAt
  have hz : HasFDerivWithinAt (fun y ↦ F (nonlinearTwoJet f y)) 0 S x :=
    (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) x).hasFDerivWithinAt.congr' he hx
  have hdw : HasFDerivWithinAt (fun y ↦ F (nonlinearTwoJet f y))
      ((fderiv ℝ F (nonlinearTwoJet f x)).comp (fderiv ℝ (nonlinearTwoJet f) x)) S x :=
    hd.hasFDerivWithinAt
  have heD := (hdw.fderivWithin (hS x hx)).symm.trans (hz.fderivWithin (hS x hx))
  have heval := congrArg (fun L : E →L[ℝ] ℝ ↦ L v) heD
  change fderiv ℝ F (nonlinearTwoJet f x) (fderiv ℝ (nonlinearTwoJet f) x v) = 0 at heval
  rw [fderiv_nonlinearTwoJet_apply hf.contDiffAt] at heval
  exact heval

theorem differentiatedResidual_normal_symbol {F : NonlinearJet E → ℝ} {f : E → ℝ}
    (hF : ContDiff ℝ 2 F) (hf : ContDiff ℝ 3 f)
    (v : E) (p : NonlinearJet E) (N : E →L[ℝ] E →L[ℝ] ℝ) :
    fderiv ℝ (differentiatedResidual F f v) p (0,N) =
      fderiv ℝ F (nonlinearTwoJet f p.1.1) (0,N) := by
  have hd := (contDiff_differentiatedResidual hF hf v).differentiable (by norm_num) p
  rw [← deriv_affine_line (0,N) hd]
  have he : (fun t : ℝ ↦ differentiatedResidual F f v (p + t • (0,N))) =
      fun t ↦ differentiatedResidual F f v p +
        t * fderiv ℝ F (nonlinearTwoJet f p.1.1) (0,N) := by
    funext t
    have hpath : p + t • (0,N) = ((p.1.1,p.1.2),p.2 + t • N) := by
      change (p.1 + t • 0,p.2 + t • N) = _
      simp
    rw [hpath]
    dsimp only [differentiatedResidual]
    have hp : ((v,p.1.2),p.2 + t • N) = ((v,p.1.2),p.2) + t • (0,N) := by simp
    rw [hp, map_add, map_smul, smul_eq_mul]
  rw [he]
  simpa only [one_mul,id_eq] using (((hasDerivAt_id (0 : ℝ)).mul_const
    (fderiv ℝ F (nonlinearTwoJet f p.1.1) (0,N))).const_add
      (differentiatedResidual F f v p)).deriv

end OAI.Analysis.PDE.Dirichlet
