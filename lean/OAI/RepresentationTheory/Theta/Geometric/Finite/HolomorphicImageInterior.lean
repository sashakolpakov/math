import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.FinitePullback
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus

/-! # Holomorphic Image Interior -/

namespace OAI.RepresentationTheory.Theta.Geometric.Finite.HolomorphicImageInterior

noncomputable section

/-! In equal dimensions, local equations for a finite holomorphic image
vanish as germs, so that image contains a neighborhood. -/

open Set Filter
open scoped _root_.Topology

theorem finite_holomorphic_image_mem_nhds
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    (hdim : Module.finrank ℂ E = Module.finrank ℂ F)
    {f : E → F} {U K : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hfinite : ∀ y : F, {z | z ∈ U ∧ f z = y}.Finite)
    {x : E} (hx : x ∈ U) (hK : K ∈ 𝓝 x)
    (hlocal : AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (f '' K) (f x)) : f '' K ∈ 𝓝 (f x) := by
  obtain ⟨V, hV, hfx, m, g, hg, heq⟩ := hlocal
  have hzero (i : Fin m) : ∀ᶠ y in 𝓝 (f x), g i y = 0 := by
    by_contra hn
    apply AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.FinitePullback.Constructions.FiniteRank.nonzero_germ_comp_of_finite_fibers hdim hU hf hfinite hV (hg i) hx hfx hn
    filter_upwards [hK,
      (hf.differentiableAt (hU.mem_nhds hx)).continuousAt.eventually (hV.mem_nhds hfx)] with z hz hzV
    exact (heq (f z) hzV).mp ⟨z, hz, rfl⟩ i
  filter_upwards [hV.mem_nhds hfx, Filter.eventually_all.mpr hzero] with y hy hgy
  exact (heq y hy).mpr hgy

end

end OAI.RepresentationTheory.Theta.Geometric.Finite.HolomorphicImageInterior
