import OAI.RepresentationTheory.Theta.Geometric.Finite.DimensionalHolomorphicInverse
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! # Manifold Chart Inverse -/

namespace OAI.RepresentationTheory.Theta.Geometric.ManifoldChartInverse

noncomputable section

/-! A holomorphic parametrization by an open partial homeomorphism has
a holomorphic coordinate inverse in equal complex dimensions. -/

set_option backward.isDefEq.respectTransparency false
open Set Filter ChartedSpace
open scoped _root_.Topology _root_.Manifold

theorem manifoldChart_holomorphic_of_inverse
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold (𝓘(ℂ, H)) 1 M]
    (hdim : Module.finrank ℂ E = Module.finrank ℂ H) (q : OpenPartialHomeomorph M E)
    (hq : MDifferentiableOn (𝓘(ℂ, E)) (𝓘(ℂ, H)) q.symm q.target)
    {x : M} (hx : x ∈ q.source) : MDifferentiableAt (𝓘(ℂ, H)) (𝓘(ℂ, E)) q x := by
  let c := chartAt H x
  have hc := mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, H)) (chart_mem_atlas H x)
  let r := q.symm.trans c
  have hr : DifferentiableOn ℂ r r.source := by
    intro z hz
    have hzq : z ∈ q.target := hz.1
    have hzc : q.symm z ∈ c.source := hz.2
    exact (mdifferentiableAt_iff_differentiableAt.mp
      ((hc.mdifferentiableAt hzc).comp z (hq.mdifferentiableAt (q.open_target.mem_nhds hzq)))).differentiableWithinAt
  have hqxr : q x ∈ r.source := by
    refine ⟨q.map_source hx, ?_⟩
    change q.symm (q x) ∈ c.source
    rw [q.left_inv hx]
    exact mem_chart_source H x
  have hcx : c x ∈ r.target := by
    have h := r.map_source hqxr
    change c (q.symm (q x)) ∈ r.target at h
    rwa [q.left_inv hx] at h
  have hri := Finite.DimensionalHolomorphicInverse.finiteDimensional_holomorphic_homeomorph_inverse hdim r hr
  have hd := (mdifferentiableAt_iff_differentiableAt.mpr
    (hri.differentiableAt (r.open_target.mem_nhds hcx))).comp x (hc.mdifferentiableAt (mem_chart_source H x))
  apply hd.congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds (mem_chart_source H x)] with y hy
  change q y = q (c.symm (c y))
  exact congrArg q (c.left_inv hy).symm

end

end OAI.RepresentationTheory.Theta.Geometric.ManifoldChartInverse
