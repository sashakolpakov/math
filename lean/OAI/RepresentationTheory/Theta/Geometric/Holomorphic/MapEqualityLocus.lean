import OAI.RepresentationTheory.Theta.Geometric.ConnectedAnalyticLocus
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! # Map Equality Locus -/

namespace OAI.RepresentationTheory.Theta.Geometric.Holomorphic.MapEqualityLocus

noncomputable section

/-! Equality of two holomorphic maps into a complex manifold is locally
defined by holomorphic scalar equations on the original open domain. -/

open Set Filter
open scoped _root_.Manifold ContDiff _root_.Topology

open OAI.Geometry.ComplexTorus.RiemannProjectivity.AnalyticIrreducibilityEq.Constructions.AnalyticIrreducibility

theorem holomorphic_map_equality_local_equations
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {d : ℕ}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (Fin d → ℂ) M]
    [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 M]
    {U : Set E} (hU : IsOpen U) {f g : E → M}
    (hf : MDifferentiableOn (𝓘(ℂ, E)) (𝓘(ℂ, Fin d → ℂ)) f U)
    (hg : MDifferentiableOn (𝓘(ℂ, E)) (𝓘(ℂ, Fin d → ℂ)) g U)
    {x : E} (hx : x ∈ U) : OAI.Geometry.ComplexTorus.RiemannProjectivity.AnalyticIrreducibilityEq.Constructions.AnalyticIrreducibility.HasLocalEquations {y | f y = g y} x := by
  classical
  by_cases he : f x = g x
  · let e := chartAt (Fin d → ℂ) (f x)
    have hfx : f x ∈ e.source := mem_chart_source _ _
    have hgx : g x ∈ e.source := he ▸ hfx
    have hfc := (hf x hx).continuousWithinAt.continuousAt (hU.mem_nhds hx)
    have hgc := (hg x hx).continuousWithinAt.continuousAt (hU.mem_nhds hx)
    have hn : {y | y ∈ U ∧ f y ∈ e.source ∧ g y ∈ e.source} ∈ 𝓝 x := by
      filter_upwards [hU.mem_nhds hx, hfc.preimage_mem_nhds (e.open_source.mem_nhds hfx),
        hgc.preimage_mem_nhds (e.open_source.mem_nhds hgx)] with y hy hf hy'
      exact ⟨hy, hf, hy'⟩
    obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp hn
    let F : Fin d → E → ℂ := fun i y => e (f y) i - e (g y) i
    refine ⟨V, hV, hxV, Set.range F, ?_, ?_⟩
    · rintro l ⟨i, rfl⟩ y hy
      have hf' : DifferentiableAt ℂ (fun z => e (f z)) y := by
        have H := ((mdifferentiable_chart (I := 𝓘(ℂ, Fin d → ℂ)) (f x)).mdifferentiableAt
          (hVsub hy).2.1).comp y ((hf y (hVsub hy).1).mdifferentiableAt (hU.mem_nhds (hVsub hy).1))
        exact mdifferentiableAt_iff_differentiableAt.mp H
      have hg' : DifferentiableAt ℂ (fun z => e (g z)) y := by
        have H := ((mdifferentiable_chart (I := 𝓘(ℂ, Fin d → ℂ)) (f x)).mdifferentiableAt
          (hVsub hy).2.2).comp y ((hg y (hVsub hy).1).mdifferentiableAt (hU.mem_nhds (hVsub hy).1))
        exact mdifferentiableAt_iff_differentiableAt.mp H
      exact (((differentiableAt_pi.mp hf') i).sub ((differentiableAt_pi.mp hg') i)).differentiableWithinAt
    · intro y hy
      constructor
      · intro h l hl
        obtain ⟨i, rfl⟩ := hl
        change e (f y) i - e (g y) i = 0
        rw [h, sub_self]
      · intro h
        apply e.injOn (hVsub hy).2.1 (hVsub hy).2.2
        funext i
        exact sub_eq_zero.mp (h (F i) ⟨i, rfl⟩)
  · let Z : Set U := {y | f y.val = g y.val}
    have hZ : IsClosed Z := isClosed_eq
      (continuousOn_iff_continuous_domRestrict.mp hf.continuousOn)
      (continuousOn_iff_continuous_domRestrict.mp hg.continuousOn)
    let V := (Subtype.val : U → E) '' Zᶜ
    have hV : IsOpen V := hU.isOpenMap_subtype_val _ hZ.isOpen_compl
    refine ⟨V, hV, ⟨⟨x, hx⟩, he, rfl⟩, {fun _ => (1 : ℂ)}, ?_, ?_⟩
    · intro l hl
      obtain rfl := Set.mem_singleton_iff.mp hl
      exact (show DifferentiableOn ℂ (fun _ : E => (1 : ℂ)) V from differentiableOn_const 1)
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := hy
      constructor
      · intro h
        exact (hz h).elim
      · intro h
        exact (one_ne_zero (h (fun _ => (1 : ℂ)) (Set.mem_singleton _))).elim

end

end OAI.RepresentationTheory.Theta.Geometric.Holomorphic.MapEqualityLocus
