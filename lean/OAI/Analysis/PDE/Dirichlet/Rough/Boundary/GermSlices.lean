import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.ChartShift

noncomputable section
open Set Filter
open scoped Topology
namespace OAI.Analysis.PDE.Dirichlet

variable {E F : Type*} [TopologicalSpace E]

/-- A joint germ of chart translations gives one open spatial neighborhood
on which every scalar parameter curve has the required translation germ. -/
theorem exists_open_parameter_germ_slices
    {f g : ℝ × E → F} {x : E} (h : f =ᶠ[𝓝 (0, x)] g) :
    ∃ O : Set E, IsOpen O ∧ x ∈ O ∧ ∀ y ∈ O,
      (fun t : ℝ ↦ f (t, y)) =ᶠ[𝓝 0] fun t ↦ g (t, y) := by
  rw [nhds_prod_eq] at h
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp h
  obtain ⟨O, hOV, hO, hxO⟩ := mem_nhds_iff.mp hV
  refine ⟨O, hO, hxO, ?_⟩
  intro y hy
  filter_upwards [hU] with t ht
  exact hUV ⟨ht, hOV hy⟩

end OAI.Analysis.PDE.Dirichlet
