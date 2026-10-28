import OAI.Analysis.PDE.Elliptic.Boundary.PullbackEllipticity
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Filter
open scoped Topology

theorem second_fderiv_comp
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : E → F} {f : F → G} {x : E}
    (hf : ContDiffAt ℝ 2 f (g x)) (hg : ContDiffAt ℝ 2 g x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => f (g y))) x v w =
      fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x v) (fderiv ℝ g x w) +
      fderiv ℝ f (g x) (fderiv ℝ (fderiv ℝ g) x v w) := by
  have hfg : (fun y => fderiv ℝ (fun z => f (g z)) y) =ᶠ[𝓝 x]
      (fun y => (fderiv ℝ f (g y)).comp (fderiv ℝ g y)) := by
    filter_upwards [hg.eventually (by norm_num),
      hg.continuousAt.tendsto.eventually (hf.eventually (by norm_num))] with y hgy hfy
    exact fderiv_fun_comp y (hfy.differentiableAt (by norm_num)) (hgy.differentiableAt (by norm_num))
  have h1 := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt.comp x
    (hg.differentiableAt (by norm_num)).hasFDerivAt
  have h2 := ((hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hd := h1.clm_comp h2
  have he := hfg.fderiv_eq.trans hd.fderiv
  have hh := congrArg (fun L => L v w) he
  simpa [ContinuousLinearMap.comp_apply, add_comm] using hh

end OAI.Analysis.PDE.Elliptic
