import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Immersion
import OAI.Geometry.ComplexTorus.RiemannProjectivity.Fin

/-! # Immersion Factor At -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.ImmersionFactorAt.Constructions.ImmersionFactor

noncomputable section

/-! # RiemannProjectivity: holomorphicity can be checked after an immersion -/

open Set Filter
open scoped _root_.Topology

variable {V W Z : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z] [FiniteDimensional ℂ Z]

theorem differentiableAt_of_comp {g : V → W} {f : W → Z} {x : V} {U : Set W}
    (hU : IsOpen U) (hx : g x ∈ U) (hf : DifferentiableOn ℂ f U)
    (hi : Function.Injective (fderiv ℂ f (g x)))
    (hg : ContinuousAt g x) (hcomp : DifferentiableAt ℂ (f ∘ g) x) : DifferentiableAt ℂ g x := by
  obtain ⟨C, q, hxq, hq, _, hqi⟩ := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Immersion.Constructions.Regularity.exists_holomorphic_normal_chart hU hf hx hi
  have hzero (w : W) : q (w, 0) = f w := by
    simpa only [ZeroMemClass.coe_zero, add_zero] using hq (w, 0)
  have htarget : f (g x) ∈ q.target := hzero (g x) ▸ q.map_source hxq
  have hd := differentiableAt_fst.comp x
    ((hqi.differentiableAt (q.open_target.mem_nhds htarget)).comp x hcomp)
  apply hd.congr_of_eventuallyEq
  have hnear : ∀ᶠ y in 𝓝 x, (g y, (0 : C)) ∈ q.source :=
    (hg.prodMk continuousAt_const).preimage_mem_nhds (q.open_source.mem_nhds hxq)
  filter_upwards [hnear] with y hy
  change g y = (q.symm (f (g y))).1
  rw [← hzero, q.left_inv hy]

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.ImmersionFactorAt.Constructions.ImmersionFactor
