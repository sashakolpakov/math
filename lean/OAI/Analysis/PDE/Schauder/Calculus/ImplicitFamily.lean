import OAI.Analysis.PDE.Schauder.Calculus.ImplicitCurve

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Schauder

variable {Z X Y : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

/-- Genuine smooth implicit solutions for an arbitrary normed parameter space. -/
theorem exists_smooth_implicit_family
    (Q : Z × X → Y) (z₀ : Z) (v₀ : X)
    (hQ : ContDiffAt ℝ ∞ Q (z₀,v₀)) (hzero : Q (z₀,v₀) = 0)
    (hder : ((fderiv ℝ Q (z₀,v₀)).comp (ContinuousLinearMap.inr ℝ Z X)).IsInvertible)
    {N : Set (Z × X)} (hN : N ∈ 𝓝 (z₀,v₀)) :
    ∃ v : Z → X, ContDiffAt ℝ ∞ v z₀ ∧ v z₀ = v₀ ∧
      ∀ᶠ z in 𝓝 z₀, (z,v z) ∈ N ∧ Q (z,v z) = 0 := by
  let v := hQ.implicitFunction (by simp) hder
  have hv : ContDiffAt ℝ ∞ v z₀ := hQ.contDiffAt_implicitFunction (by simp) hder
  have hv0 : v z₀ = v₀ := hQ.implicitFunction_apply_self (by simp) hder
  have hp : Tendsto (fun z => (z,v z)) (𝓝 z₀) (𝓝 (z₀,v₀)) := by
    simpa only [hv0,id_eq] using continuousAt_id.tendsto.prodMk_nhds hv.continuousAt.tendsto
  refine ⟨v,hv,hv0,?_⟩
  filter_upwards [hp hN,hQ.eventually_apply_implicitFunction (by simp) hder] with z hz he
  exact ⟨hz,he.trans hzero⟩

end OAI.Analysis.PDE.Schauder
