import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.Implicit

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Schauder

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- The actual implicit curve, kept in any prescribed neighborhood of its
base point. No continuity of a separately specified geometric action is used. -/
theorem exists_smooth_implicit_curve
    (Q : ℝ × X → Y) (v₀ : X)
    (hQ : ContDiffAt ℝ ∞ Q (0,v₀)) (hzero : Q (0,v₀) = 0)
    (hder : ((fderiv ℝ Q (0,v₀)).comp (ContinuousLinearMap.inr ℝ ℝ X)).IsInvertible)
    {N : Set (ℝ × X)} (hN : N ∈ 𝓝 (0,v₀)) :
    ∃ v : ℝ → X, ContDiffAt ℝ ∞ v 0 ∧ v 0 = v₀ ∧
      ∀ᶠ t in 𝓝 0, (t,v t) ∈ N ∧ Q (t,v t) = 0 := by
  let v := hQ.implicitFunction (by simp) hder
  have hv : ContDiffAt ℝ ∞ v 0 := hQ.contDiffAt_implicitFunction (by simp) hder
  have hv0 : v 0 = v₀ := hQ.implicitFunction_apply_self (by simp) hder
  have hp : Tendsto (fun t => (t,v t)) (𝓝 0) (𝓝 (0,v₀)) := by
    simpa only [hv0,id_eq] using continuousAt_id.tendsto.prodMk_nhds hv.continuousAt.tendsto
  refine ⟨v,hv,hv0,?_⟩
  filter_upwards [hp hN,hQ.eventually_apply_implicitFunction (by simp) hder] with t ht he
  exact ⟨ht,he.trans hzero⟩

end OAI.Analysis.PDE.Schauder
