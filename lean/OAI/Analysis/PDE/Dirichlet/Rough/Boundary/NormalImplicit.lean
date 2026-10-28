import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.Implicit

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

variable {E X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- A continuous solution of a nondegenerate implicit equation inherits its
finite differentiability. Used for the pure normal Hessian component. -/
theorem contDiffAt_of_continuous_implicit_equation
    (Q : E × X → Y) (u : E → X) {x : E} {q : ℕ∞ω}
    (hQ : ContDiffAt ℝ q Q (x, u x)) (hq : q ≠ 0)
    (hD : ((fderiv ℝ Q (x, u x)).comp (ContinuousLinearMap.inr ℝ E X)).IsInvertible)
    (hu : ContinuousAt u x)
    (he : ∀ᶠ y in 𝓝 x, Q (y, u y) = Q (x, u x)) :
    ContDiffAt ℝ q u x := by
  let g : E → X := hQ.implicitFunction hq hD
  have hg : ContDiffAt ℝ q g x := hQ.contDiffAt_implicitFunction hq hD
  have ht : Tendsto (fun y ↦ (y, u y)) (𝓝 x) (𝓝 (x, u x)) :=
    (continuousAt_id.prodMk hu).tendsto
  have hiff := ht.eventually (hQ.eventually_apply_eq_iff_implicitFunction hq hD)
  have heq : u =ᶠ[𝓝 x] g := by
    filter_upwards [he, hiff] with y hy hiy
    exact (hiy.mp hy).symm
  exact hg.congr_of_eventuallyEq heq

end OAI.Analysis.PDE.Dirichlet
