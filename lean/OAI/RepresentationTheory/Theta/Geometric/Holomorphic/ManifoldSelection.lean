import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.MapEqualityLocus
import OAI.RepresentationTheory.Theta.Geometric.AnalyticCountableSelection

/-! # Manifold Selection -/

namespace OAI.RepresentationTheory.Theta.Geometric.Holomorphic.ManifoldSelection

noncomputable section

section

/-! Holomorphic uniqueness and countable selection for maps into actual
complex manifolds, including native scheme manifolds. -/

open Set Filter
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {d : ℕ}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (Fin d → ℂ) M]
    [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 M]
    {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U)
    {f g : E → M}
    (hf : MDifferentiableOn (𝓘(ℂ, E)) (𝓘(ℂ, Fin d → ℂ)) f U)
    (hg : MDifferentiableOn (𝓘(ℂ, E)) (𝓘(ℂ, Fin d → ℂ)) g U)

include hU hc hf hg in
theorem holomorphic_manifold_identity {x : E} (hx : x ∈ U) (hfg : f =ᶠ[𝓝 x] g) :
    Set.EqOn f g U := by
  apply ConnectedAnalyticLocus.connected_local_equations_eq_on hc
    (fun y hy => MapEqualityLocus.holomorphic_map_equality_local_equations hU hf hg hy)
  exact ⟨x, hx, mem_interior_iff_mem_nhds.mpr hfg⟩

include hU hc hf in
theorem holomorphic_manifold_countable_selection [BaireSpace E]
    {I : Type*} [Countable I] (hne : U.Nonempty) {g : I → E → M}
    (hg : ∀ i, MDifferentiableOn (𝓘(ℂ, E)) (𝓘(ℂ, Fin d → ℂ)) (g i) U)
    (hcover : ∀ x ∈ U, ∃ i, f x = g i x) : ∃ i, Set.EqOn f (g i) U := by
  let : BaireSpace U := hU.baireSpace
  let : Nonempty U := hne.to_subtype
  let Z : I → Set U := fun i => {x | f x.val = g i x.val}
  have hZ (i : I) : IsClosed (Z i) :=
    isClosed_eq (continuousOn_iff_continuous_domRestrict.mp hf.continuousOn)
      (continuousOn_iff_continuous_domRestrict.mp (hg i).continuousOn)
  have hZU : ⋃ i, Z i = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact hcover x.val x.property
  obtain ⟨i, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hZ hZU
  refine ⟨i, holomorphic_manifold_identity hU hc hf (hg i) x.property ?_⟩
  have hV : IsOpen ((Subtype.val : U → E) '' interior (Z i)) := hU.isOpenMap_subtype_val _ isOpen_interior
  have hxV : x.val ∈ ((Subtype.val : U → E) '' interior (Z i)) := ⟨x, hx, rfl⟩
  filter_upwards [hV.mem_nhds hxV] with y hy
  obtain ⟨z, hz, rfl⟩ := hy
  exact (show z ∈ Z i from interior_subset hz)

end

/-! Countable holomorphic selection on the actual open ball subtype,
without requiring ambient extensions in its interface. -/

open Set
open scoped Classical _root_.Manifold ContDiff

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [BaireSpace E]
    {d : ℕ} [TopologicalSpace M] [T2Space M] [ChartedSpace (Fin d → ℂ) M]
    [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 M]
    (U : TopologicalSpace.Opens E) [Nonempty U]

private def openMapExtension (f : U → M) (x : E) : M :=
  if h : x ∈ U then f ⟨x, h⟩ else f (Classical.choice inferInstance)

omit [NormedSpace ℂ E] [BaireSpace E] [TopologicalSpace M] [T2Space M] in
private theorem openMapExtension_value (f : U → M) (x : U) :
    openMapExtension U f x.val = f x := by
  simp only [openMapExtension, dite_eq_left x.property]

omit [IsManifold (𝓘(ℂ, Fin d → ℂ)) 1 M] [BaireSpace E] [T2Space M] in
private theorem openMapExtension_holomorphic (f : U → M)
    (hf : ContMDiff (𝓘(ℂ, E)) (𝓘(ℂ, Fin d → ℂ)) 1 f) :
    MDifferentiableOn (𝓘(ℂ, E)) (𝓘(ℂ, Fin d → ℂ)) (openMapExtension U f) U := by
  have H : ContMDiff (𝓘(ℂ, E)) (𝓘(ℂ, Fin d → ℂ)) 1
      (fun x : U => openMapExtension U f x.val) := by
    simpa only [openMapExtension_value] using hf
  intro x hx
  have h := (contMDiffAt_subtype_iff.mp (H ⟨x, hx⟩)).mdifferentiableAt one_ne_zero
  exact h.mdifferentiableWithinAt

theorem open_holomorphic_countable_selection (hc : IsPreconnected (U : Set E))
    {I : Type*} [Countable I] (f : U → M) (g : I → U → M)
    (hf : ContMDiff (𝓘(ℂ, E)) (𝓘(ℂ, Fin d → ℂ)) 1 f)
    (hg : ∀ i, ContMDiff (𝓘(ℂ, E)) (𝓘(ℂ, Fin d → ℂ)) 1 (g i))
    (hcover : ∀ x, ∃ i, f x = g i x) : ∃ i, f = g i := by
  obtain ⟨i, hi⟩ := holomorphic_manifold_countable_selection U.isOpen hc
    (openMapExtension_holomorphic U f hf)
    (show (U : Set E).Nonempty from ⟨(Classical.choice inferInstance : U).val,
      (Classical.choice inferInstance : U).property⟩)
    (fun i => openMapExtension_holomorphic U (g i) (hg i))
    (fun x hx => by
      obtain ⟨i, hi⟩ := hcover ⟨x, hx⟩
      exact ⟨i, (openMapExtension_value U f ⟨x, hx⟩).trans
        (hi.trans (openMapExtension_value U (g i) ⟨x, hx⟩).symm)⟩)
  refine ⟨i, funext fun x => ?_⟩
  simpa only [openMapExtension_value] using hi x.property

end

end OAI.RepresentationTheory.Theta.Geometric.Holomorphic.ManifoldSelection
