import OAI.AlgebraicGeometry.CycleClass.Thom.Open.EmbeddingComplexChart
import OAI.AlgebraicGeometry.CycleClass.Thom.Product.PointCanonical

/-! # Embedding Chart Point -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.EmbeddingChartPoint.Constructions.Class

noncomputable section

/-! Canonical point classes restrict along actual open embeddings into a specified global chart. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.SingleChartComplexManifold.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.EmbeddingComplexChart.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.CanonicalLocalDual.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.LocalDualLocalInverse.Constructions.CanonicalNaturality OAI.AlgebraicGeometry.CycleClass.Thom.Product.PointCanonical.Constructions.Class

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem canonicalPoint_restriction (d : ℕ) {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y] [Nonempty X] [Nonempty Y]
    (e : Y ≃ₜ (Fin d → ℂ)) (f : TopCat.of X ⟶ TopCat.of Y)
    (hf : Topology.IsOpenEmbedding f) (x : X) :
    letI := SingleChartComplexManifold.Constructions.coordinateChartedSpace d e
    letI := Open.EmbeddingComplexChart.Constructions.embeddingChartedSpace d (e ∘ f) (e.isOpenEmbedding.comp hf)
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) f (LocalDualLocalInverse.Constructions.CanonicalNaturality.injectivePunctureMapsTo f hf.injective x)
      (2 * d) (CanonicalLocalDual.Constructions.canonicalLocalDual d (f x)) = CanonicalLocalDual.Constructions.canonicalLocalDual d x := by
  let := SingleChartComplexManifold.Constructions.coordinateChartedSpace d e
  let := Open.EmbeddingComplexChart.Constructions.embeddingChartedSpace d (e ∘ f) (e.isOpenEmbedding.comp hf)
  let := Open.EmbeddingComplexChart.Constructions.embeddingManifold d (e ∘ f) (e.isOpenEmbedding.comp hf)
  let j : TopCat.of X ⟶ TopCat.of (Fin d → ℂ) :=
    f ≫ (TopCat.isoOfHomeo (X := TopCat.of Y) (Y := TopCat.of (Fin d → ℂ)) e).hom
  have hfull := SingleChartComplexManifold.Constructions.pointClass_chart d e (f x)
  rw [← hfull]
  have hc := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) f
      (TopCat.isoOfHomeo (X := TopCat.of Y) (Y := TopCat.of (Fin d → ℂ)) e).hom
      (LocalDualLocalInverse.Constructions.CanonicalNaturality.injectivePunctureMapsTo f hf.injective x)
      (LocalDualLocalInverse.Constructions.CanonicalNaturality.injectivePunctureMapsTo _ e.injective (f x)) (2 * d)) (CanonicalLocalDual.Constructions.canonicalLocalDual d (e (f x)))
  refine hc.trans ?_
  exact LocalDualLocalInverse.Constructions.CanonicalNaturality.canonicalLocalDual_pullback d j (e.injective.comp hf.injective)
    (Open.EmbeddingComplexChart.Constructions.embedding_localDiffeomorph d (e ∘ f) (e.isOpenEmbedding.comp hf)) x

end

end OAI.AlgebraicGeometry.CycleClass.Thom.EmbeddingChartPoint.Constructions.Class
