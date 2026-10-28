import OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.OpenAmbient
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.KernelBaseChange

/-! # Open Square -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.OpenSquare.BundleCycles

noncomputable section

/-! The graph of the restricted morphism is the actual scheme-theoretic open base change of the original graph. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {X Y X' Y' : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (g : X'.toOver ⟶ Y'.toOver)
    (a : X'.toOver ⟶ X.toOver) (b : Y'.toOver ⟶ Y.toOver)
    [IsOpenImmersion a.left] [IsOpenImmersion b.left] (h : a ≫ f = g ≫ b)

include h in
theorem graphOpenAmbientMap_graph_preimage :
    OpenAmbient.BundleCycles.graph f ⁻¹ᵁ (OpenAmbient.BundleCycles.graphOpenAmbientMap f g a b).opensRange = a.left.opensRange := by
  apply TopologicalSpace.Opens.ext
  ext x
  change OpenAmbient.BundleCycles.graph f x ∈ Set.range (OpenAmbient.BundleCycles.graphOpenAmbientMap f g a b) ↔ x ∈ Set.range a.left
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨OpenAmbient.BundleCycles.graphFirstProjection g u, ?_⟩
    exact (congrArg (fun k => k u) (OpenAmbient.BundleCycles.graphOpenAmbientMap_first f g a b)).symm.trans
      ((congrArg (OpenAmbient.BundleCycles.graphFirstProjection f) hu).trans (congrArg (fun k => k x) (OpenAmbient.BundleCycles.graph_firstProjection f)))
  · rintro ⟨u, rfl⟩
    exact ⟨OpenAmbient.BundleCycles.graph g u, congrArg (fun k => k u) (OpenAmbient.BundleCycles.graphOpenAmbientMap_graph f g a b h)⟩

include h in
theorem graphOpenAmbientMap_isPullback :
    IsPullback (OpenAmbient.BundleCycles.graph g) a.left (OpenAmbient.BundleCycles.graphOpenAmbientMap f g a b) (OpenAmbient.BundleCycles.graph f) :=
  @IsOpenImmersion.isPullback _ _ _ _ (OpenAmbient.BundleCycles.graph g) a.left (OpenAmbient.BundleCycles.graphOpenAmbientMap f g a b) (OpenAmbient.BundleCycles.graph f)
    (inferInstanceAs (IsOpenImmersion a.left)) (OpenAmbient.BundleCycles.graphOpenAmbientMap_open f g a b)
    (OpenAmbient.BundleCycles.graphOpenAmbientMap_graph f g a b h).symm
    (graphOpenAmbientMap_graph_preimage f g a b h)

include h in
theorem graphOpenAmbientMap_kernel :
    (OpenAmbient.BundleCycles.graph f).ker.comap (OpenAmbient.BundleCycles.graphOpenAmbientMap f g a b) = (OpenAmbient.BundleCycles.graph g).ker :=
  Open.KernelBaseChange.BundleCycles.openKernel_comap_of_isPullback (OpenAmbient.BundleCycles.graph f) (OpenAmbient.BundleCycles.graph g) a.left (OpenAmbient.BundleCycles.graphOpenAmbientMap f g a b)
    (graphOpenAmbientMap_isPullback f g a b h)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graph.OpenSquare.BundleCycles
