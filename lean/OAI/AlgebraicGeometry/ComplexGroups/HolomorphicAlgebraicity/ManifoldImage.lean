import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Immersion
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! # Manifold Image -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ManifoldImage.Constructions.Cone

noncomputable section

section

/-!
# Local equations for holomorphic images of complex manifolds

The equations come from the proved finite-dimensional normal-chart theorem.
The embedding hypothesis excludes additional image branches near the point.
-/

open Set ChartedSpace
open scoped _root_.Manifold _root_.Topology

/-- An embedded holomorphic immersion, on any open part of a finite-dimensional
complex manifold, has an image locally cut out by holomorphic equations. -/
theorem holomorphicZeroSetAt_manifold_image
    {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℂ, E)) 1 M]
    {U : Set M} (hU : IsOpen U) {f : M → F}
    (hf : MDifferentiableOn (𝓘(ℂ, E)) (𝓘(ℂ, F)) f U)
    (hemb : Topology.IsEmbedding (fun z : U => f z))
    {x : M} (hx : x ∈ U)
    (hinj : Function.Injective (mfderiv (𝓘(ℂ, E)) (𝓘(ℂ, F)) f x)) :
    ZeroLocus.Constructions.Cone.HolomorphicZeroSetAt (f '' U) (f x) := by
  let e := chartAt E x
  let V : Set E := e.target ∩ e.symm ⁻¹' U
  let g : E → F := f ∘ e.symm
  have he : e.MDifferentiable (𝓘(ℂ, E)) (𝓘(ℂ, E)) := mdifferentiable_chart x
  have hV : IsOpen V := e.isOpen_inter_preimage_symm hU
  have hxe : x ∈ e.source := mem_chart_source E x
  have hxV : e x ∈ V :=
    ⟨e.map_source hxe, by simpa only [mem_preimage, e.left_inv hxe] using hx⟩
  have hg : DifferentiableOn ℂ g V := by
    intro z hz
    have hF := (hf _ hz.2).mdifferentiableAt (hU.mem_nhds hz.2)
    exact ((hF.comp z (he.mdifferentiableAt_symm hz.1)).differentiableAt).differentiableWithinAt
  have hemb_e : Topology.IsEmbedding (fun z : V => e.symm z) :=
    e.symm.isEmbedding_restrict.comp (Topology.IsEmbedding.inclusion inter_subset_left)
  have hemb_g : Topology.IsEmbedding (fun z : V => g z) :=
    hemb.comp (hemb_e.codRestrict U (fun z => z.property.2))
  have hinj_g : Function.Injective (fderiv ℂ g (e x)) := by
    rw [← mfderiv_eq_fderiv]
    change Function.Injective (mfderiv (𝓘(ℂ, E)) (𝓘(ℂ, F)) (f ∘ e.symm) (e x))
    have hF : MDifferentiableAt (𝓘(ℂ, E)) (𝓘(ℂ, F)) f (e.symm (e x)) := by
      rw [e.left_inv hxe]
      exact (hf x hx).mdifferentiableAt (hU.mem_nhds hx)
    rw [mfderiv_comp (e x) hF (he.mdifferentiableAt_symm hxV.1)]
    have hfi : Function.Injective (mfderiv (𝓘(ℂ, E)) (𝓘(ℂ, F)) f (e.symm (e x))) := by
      rw [e.left_inv hxe]
      exact hinj
    exact hfi.comp (he.symm.mfderiv_injective hxV.1)
  have hz := Immersion.Constructions.Cone.holomorphicZeroSetAt_image_of_embedding hV hg hemb_g hxV hinj_g
  have hgx : g (e x) = f x := by simp only [g, Function.comp_apply, e.left_inv hxe]
  rw [hgx] at hz
  let W : Set U := {z | z.val ∈ e.source}
  have hW : IsOpen W := e.open_source.preimage continuous_subtype_val
  obtain ⟨O, hO, hOp⟩ := hemb.isInducing.isOpen_iff.mp hW
  have hxO : f x ∈ O := by
    change (⟨x, hx⟩ : U) ∈ (fun z : U => f z) ⁻¹' O
    rw [hOp]
    exact hxe
  apply hz.congr
  filter_upwards [hO.mem_nhds hxO] with y hy
  constructor
  · rintro ⟨a, ha, hay⟩
    have hae : a ∈ e.source := by
      change (⟨a, ha⟩ : U) ∈ W
      rw [← hOp]
      change f a ∈ O
      rw [hay]
      exact hy
    refine ⟨e a, ⟨e.map_source hae, ?_⟩, ?_⟩
    · simpa only [mem_preimage, e.left_inv hae] using ha
    · simpa only [g, Function.comp_apply, e.left_inv hae] using hay
  · rintro ⟨a, ha, hay⟩
    exact ⟨e.symm a, ha.2, hay⟩

end

/-!
# Local holomorphic parametrizations of embedded manifold images
-/

open Set ChartedSpace
open scoped _root_.Manifold _root_.Topology

theorem local_parametrization_of_manifold_image
    {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℂ, E)) 1 M]
    {U : Set M} (hU : IsOpen U) {f : M → F}
    (hf : MDifferentiableOn (𝓘(ℂ, E)) (𝓘(ℂ, F)) f U)
    (hemb : Topology.IsEmbedding (fun z : U => f z))
    {x : M} (hx : x ∈ U) :
    ∃ (O : Set F) (V : Set E) (g : E → F),
      IsOpen O ∧ f x ∈ O ∧ IsOpen V ∧ DifferentiableOn ℂ g V ∧
      (f '' U) ∩ O ⊆ g '' V ∧ MapsTo g V (f '' U) ∧ InjOn g V := by
  let e := chartAt E x
  let V : Set E := e.target ∩ e.symm ⁻¹' U
  let g : E → F := f ∘ e.symm
  have he : e.MDifferentiable (𝓘(ℂ, E)) (𝓘(ℂ, E)) := mdifferentiable_chart x
  have hV : IsOpen V := e.isOpen_inter_preimage_symm hU
  have hxe : x ∈ e.source := mem_chart_source E x
  have hg : DifferentiableOn ℂ g V := by
    intro z hz
    have hF := (hf _ hz.2).mdifferentiableAt (hU.mem_nhds hz.2)
    exact ((hF.comp z (he.mdifferentiableAt_symm hz.1)).differentiableAt).differentiableWithinAt
  have hemb_e : Topology.IsEmbedding (fun z : V => e.symm z) :=
    e.symm.isEmbedding_restrict.comp (Topology.IsEmbedding.inclusion inter_subset_left)
  have hemb_g : Topology.IsEmbedding (fun z : V => g z) :=
    hemb.comp (hemb_e.codRestrict U (fun z => z.property.2))
  let W : Set U := {z | z.val ∈ e.source}
  have hW : IsOpen W := e.open_source.preimage continuous_subtype_val
  obtain ⟨O, hO, hOp⟩ := hemb.isInducing.isOpen_iff.mp hW
  have hxO : f x ∈ O := by
    change (⟨x, hx⟩ : U) ∈ (fun z : U => f z) ⁻¹' O
    rw [hOp]
    exact hxe
  refine ⟨O, V, g, hO, hxO, hV, hg, ?_, ?_, ?_⟩
  · rintro y ⟨⟨a, ha, hay⟩, hy⟩
    have hae : a ∈ e.source := by
      change (⟨a, ha⟩ : U) ∈ W
      rw [← hOp]
      change f a ∈ O
      rw [hay]
      exact hy
    refine ⟨e a, ⟨e.map_source hae, ?_⟩, ?_⟩
    · simpa only [mem_preimage, e.left_inv hae] using ha
    · simpa only [g, Function.comp_apply, e.left_inv hae] using hay
  · intro z hz
    exact ⟨e.symm z, hz.2, rfl⟩
  · intro z hz w hw hzw
    exact congrArg Subtype.val (hemb_g.injective (a₁ := ⟨z, hz⟩) (a₂ := ⟨w, hw⟩) hzw)

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ManifoldImage.Constructions.Cone
