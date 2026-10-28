import Mathlib

/-! # Local Lifts -/

namespace OAI.Geometry.ComplexBall.LocalLifts.ArithmeticQuotient

noncomputable section

/-! Two continuous local lifts through a local homeomorphism which agree
at a point agree on a neighborhood of that point. -/

open _root_.Topology Filter

lemma local_lifts_eventuallyEq {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {f : X → Y} (hf : IsLocalHomeomorph f) {u v : Z → X} {z : Z}
    (hu : ContinuousAt u z) (hv : ContinuousAt v z) (he : u z = v z)
    (hcomp : (fun t => f (u t)) =ᶠ[𝓝 z] (fun t => f (v t))) : u =ᶠ[𝓝 z] v := by
  let e := hf.localInverseAt (u z)
  have hx : u z ∈ e.target := hf.self_mem_localInverseAt_target
  have hy : v z ∈ e.target := he ▸ hx
  have hu' : ∀ᶠ t in 𝓝 z, u t ∈ e.target := hu (e.open_target.mem_nhds hx)
  have hv' : ∀ᶠ t in 𝓝 z, v t ∈ e.target := hv (e.open_target.mem_nhds hy)
  filter_upwards [hu', hv', hcomp] with t hut hvt ht
  exact hf.injOn_localInverseAt_target hut hvt ht

end

end OAI.Geometry.ComplexBall.LocalLifts.ArithmeticQuotient
