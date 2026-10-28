import OAI.Analysis.PDE.Elliptic.Boundary.ChainRule

/-! The actual third Fréchet derivative under a boundary coordinate change. -/

noncomputable section
open Filter
open scoped Topology
namespace OAI.Analysis.PDE.Elliptic

theorem third_fderiv_comp
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : E → F} {f : F → G} {x : E}
    (hf : ContDiffAt ℝ 3 f (g x)) (hg : ContDiffAt ℝ 3 g x) (q v w : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => f (g y)))) x q v w =
      fderiv ℝ (fderiv ℝ (fderiv ℝ f)) (g x)
        (fderiv ℝ g x q) (fderiv ℝ g x v) (fderiv ℝ g x w) +
      fderiv ℝ (fderiv ℝ f) (g x)
        (fderiv ℝ (fderiv ℝ g) x q v) (fderiv ℝ g x w) +
      fderiv ℝ (fderiv ℝ f) (g x)
        (fderiv ℝ g x v) (fderiv ℝ (fderiv ℝ g) x q w) +
      fderiv ℝ (fderiv ℝ f) (g x)
        (fderiv ℝ g x q) (fderiv ℝ (fderiv ℝ g) x v w) +
      fderiv ℝ f (g x) (fderiv ℝ (fderiv ℝ (fderiv ℝ g)) x q v w) := by
  have hfd : DifferentiableAt ℝ f (g x) := hf.differentiableAt (by norm_num)
  have hgd : DifferentiableAt ℝ g x := hg.differentiableAt (by norm_num)
  have hf₁ : ContDiffAt ℝ 2 (fderiv ℝ f) (g x) := hf.fderiv_right (by norm_num)
  have hf₂ : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ f)) (g x) := hf₁.fderiv_right (by norm_num)
  have hg₁ : ContDiffAt ℝ 2 (fderiv ℝ g) x := hg.fderiv_right (by norm_num)
  have hg₂ : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ g)) x := hg₁.fderiv_right (by norm_num)
  have ha := (hf₂.differentiableAt one_ne_zero).hasFDerivAt.comp x hgd.hasFDerivAt
  have hb := (hg₁.differentiableAt (by norm_num)).hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  have hc := (hg₁.differentiableAt (by norm_num)).hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have hd := (hf₁.differentiableAt (by norm_num)).hasFDerivAt.comp x hgd.hasFDerivAt
  have he := ((hg₂.differentiableAt one_ne_zero).hasFDerivAt.clm_apply
    (hasFDerivAt_const v x)).clm_apply (hasFDerivAt_const w x)
  have hright := ((ha.clm_apply hb).clm_apply hc).add (hd.clm_apply he)
  have hfg : ContDiffAt ℝ 3 (fun y => f (g y)) x := hf.comp x hg
  have hfg₁ : ContDiffAt ℝ 2 (fderiv ℝ (fun y => f (g y))) x :=
    hfg.fderiv_right (by norm_num)
  have hfg₂ : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ (fun y => f (g y)))) x :=
    hfg₁.fderiv_right (by norm_num)
  have hleft := ((hfg₂.differentiableAt one_ne_zero).hasFDerivAt.clm_apply
    (hasFDerivAt_const v x)).clm_apply (hasFDerivAt_const w x)
  have heq : (fun y => fderiv ℝ (fderiv ℝ (fun z => f (g z))) y v w) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ (fderiv ℝ f) (g y) (fderiv ℝ g y v) (fderiv ℝ g y w) +
        fderiv ℝ f (g y) (fderiv ℝ (fderiv ℝ g) y v w)) := by
    filter_upwards [hg.eventually (by norm_num),
      hg.continuousAt.tendsto.eventually (hf.eventually (by norm_num))]
      with y hgy hfy
    exact second_fderiv_comp (hfy.of_le (by norm_num)) (hgy.of_le (by norm_num)) v w
  have hder := hleft.unique (hright.congr_of_eventuallyEq heq)
  have hval := congrArg (fun L => L q) hder
  simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    add_apply, zero_apply, map_zero, zero_add,
    add_zero, add_assoc, add_left_comm, add_comm] using hval

end OAI.Analysis.PDE.Elliptic
