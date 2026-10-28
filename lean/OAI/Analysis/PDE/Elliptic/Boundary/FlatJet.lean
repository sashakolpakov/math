import OAI.Analysis.PDE.Elliptic.Boundary.Chart.Fields

/-! Vanishing boundary values annihilate the tangential first and second jets
in actual flat coordinates, not merely in a supplied boundary chart model. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Filter InnerProductSpace
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem flat_boundary_first_jet_of_local_zero {u : E → ℝ} {z : E} (hu : DifferentiableAt ℝ u z)
    {v e : E} (hv : ‖v‖ = 1) (hvz : inner ℝ v z = 0) (he : inner ℝ v e = 0)
    (hzero : ∀ᶠ y in 𝓝 z, inner ℝ v y = 0 → u y = 0) :
    fderiv ℝ u z e = 0 := by
  let ell : E →L[ℝ] ℝ := innerSL ℝ v
  have hell : ell ≠ 0 := by
    intro hh
    have hvv := congrArg (fun L : E →L[ℝ] ℝ => L v) hh
    have hn : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
    exact one_ne_zero (hn.symm.trans (by simpa [ell] using hvv))
  apply OAI.Analysis.PDE.Dirichlet.level_set_derivative_zero ell.hasStrictFDerivAt hell hu.hasFDerivAt _ he
  filter_upwards [hzero] with y hy hlevel
  exact hy (hlevel.trans hvz)

theorem flat_boundary_first_jet {u : E → ℝ} (hu : Differentiable ℝ u)
    {v z e : E} (hv : ‖v‖ = 1) (hz : ‖z‖ < 1) (hvz : inner ℝ v z = 0)
    (he : inner ℝ v e = 0)
    (hzero : ∀ y, ‖y‖ ≤ 1 → inner ℝ v y = 0 → u y = 0) :
    fderiv ℝ u z e = 0 := by
  let ell : E →L[ℝ] ℝ := innerSL ℝ v
  have hell : ell ≠ 0 := by
    intro hh
    have hvv := congrArg (fun L : E →L[ℝ] ℝ => L v) hh
    have hn : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
    exact one_ne_zero (hn.symm.trans (by simpa [ell] using hvv))
  apply OAI.Analysis.PDE.Dirichlet.level_set_derivative_zero ell.hasStrictFDerivAt hell (hu z).hasFDerivAt _ he
  filter_upwards [Metric.isOpen_ball.mem_nhds (show z ∈ Metric.ball (0 : E) 1 by simpa using hz)] with y hy
  intro hlevel
  apply hzero y (by have := Metric.mem_ball.mp hy; simpa using this.le)
  change inner ℝ v y = inner ℝ v z at hlevel
  exact hlevel.trans hvz

theorem flat_boundary_second_jet {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    {v z e f : E} (hv : ‖v‖ = 1) (hz : ‖z‖ < 1) (hvz : inner ℝ v z = 0)
    (he : inner ℝ v e = 0) (hf : inner ℝ v f = 0)
    (hzero : ∀ y, ‖y‖ ≤ 1 → inner ℝ v y = 0 → u y = 0) :
    fderiv ℝ (fderiv ℝ u) z e f = 0 := by
  let ell : E →L[ℝ] ℝ := innerSL ℝ v
  have hell : ell ≠ 0 := by
    intro hh
    have hvv := congrArg (fun L : E →L[ℝ] ℝ => L v) hh
    have hn : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
    exact one_ne_zero (hn.symm.trans (by simpa [ell] using hvv))
  have hl : ∀ᶠ y in 𝓝 z, ell y = ell z → u y = 0 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show z ∈ Metric.ball (0 : E) 1 by simpa using hz)] with y hy
    intro hlevel
    apply hzero y (by have := Metric.mem_ball.mp hy; simpa using this.le)
    exact hlevel.trans hvz
  obtain ⟨a, ha⟩ := OAI.Analysis.PDE.Dirichlet.level_set_gradient_factor
    (by simpa only [ell.hasFDerivAt.fderiv] using ell.hasStrictFDerivAt (x := z))
    (by simpa only [ell.hasFDerivAt.fderiv] using hell) (hu.differentiable (by norm_num) z) hl
  have hder : fderiv ℝ (ell : E → ℝ) = fun _ => ell := funext fun y => ell.hasFDerivAt.fderiv
  have hh := OAI.Analysis.PDE.Dirichlet.level_set_tangent_hessian (x := z) (v := e) (z := f) ell.contDiff hu
    (by simpa only [hder] using hell) hl ha
    (by rw [hder]; exact he) (by rw [hder]; exact hf)
  simpa [hder] using hh

end OAI.Analysis.PDE.Elliptic
