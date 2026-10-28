import OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainFunctoriality

/-! # Open Immersion -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.OpenImmersion.Constructions.Raw

noncomputable section

/-! Restricting a closed holomorphic immersion to an ambient open, for arbitrary complex model spaces. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.GraphOpenImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential.Constructions.Manifold

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M N E G : Type} [TopologicalSpace M] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E M]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
  (f : M → N) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, G) ω f) (U : Opens N)

theorem restrictedBase_differential_injective
    (hi : ∀ x, Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) f x)) (x : GraphOpenImmersion.Constructions.graphSourceOpen f hf U) :
    Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) (GraphOpenImmersion.Constructions.restrictedBase f hf U) x) := by
  have hv := (show ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) 1
    (Subtype.val : GraphOpenImmersion.Constructions.graphSourceOpen f hf U → M) from contMDiff_subtype_val).mdifferentiableAt
      (x := x) one_ne_zero
  have hd := ComplexPoints.Analytic.RegularLocusComplement.mfderiv_intoOpen_eq (𝕜 := ℂ) («E» := E) (F := G) U (GraphOpenImmersion.Constructions.restrictedBase f hf U) x
  change mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) (GraphOpenImmersion.Constructions.restrictedBase f hf U) x =
    mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) (f ∘ (Subtype.val : GraphOpenImmersion.Constructions.graphSourceOpen f hf U → M)) x at hd
  rw [mfderiv_comp x ((hf x.val).mdifferentiableAt (by simp)) hv, Open.InclusionDifferential.Constructions.Manifold.mfderiv_subtypeVal] at hd
  exact (congrArg (fun L : E →L[ℂ] G => Function.Injective L) hd).mpr (hi x.val)

theorem restrictedBase_closedEmbedding (he : Topology.IsClosedEmbedding f) :
    Topology.IsClosedEmbedding (GraphOpenImmersion.Constructions.restrictedBase f hf U) :=
  (U : Set N).restrictPreimage_isClosedEmbedding he

theorem restriction_mapsTo : Set.MapsTo (Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of N) (U : Set N))
    (Set.range (GraphOpenImmersion.Constructions.restrictedBase f hf U))ᶜ (Set.range f)ᶜ := by
  intro y hy h
  obtain ⟨z, hz⟩ := h
  apply hy
  have hzU : f z ∈ U := hz.symm ▸ y.property
  exact ⟨⟨z, hzU⟩, Subtype.ext hz⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.OpenImmersion.Constructions.Raw
