import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NestedOpenPointClass
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.OpenExtensionComposition

/-! # Nested Open Trace -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NestedOpenTrace.Constructions

noncomputable section

/-! The native trace commutes with extension between any two nested ambient opens. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

theorem openEmbeddingCompactExtension_nested {X : TopCat.{0}} [T2Space X]
    {U V : Opens X} (h : U ≤ V) (n : ℕ) :
    OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension (NestedOpenPointClass.Constructions.opensInclusionMap h) (NestedOpenPointClass.Constructions.opensInclusionMap_isOpenEmbedding h) n ≫
      AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension V n = AlgebraicTopology.Duality.Poincare.CompactSupportExcision.compactSupportOpenExtension U n := by
  have hc := OpenExtensionComposition.Constructions.openEmbeddingCompactExtension_comp (NestedOpenPointClass.Constructions.opensInclusionMap h) (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X V)
    (NestedOpenPointClass.Constructions.opensInclusionMap_isOpenEmbedding h) V.isOpen.isOpenEmbedding_subtypeVal n
  have hL := OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension_openSubspace V n
  have hR := OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension_openSubspace U n
  exact (congrArg (fun v => OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension (NestedOpenPointClass.Constructions.opensInclusionMap h)
    (NestedOpenPointClass.Constructions.opensInclusionMap_isOpenEmbedding h) n ≫ v) hL.symm).trans (hc.trans hR)

theorem complexManifoldTrace_openInclusion {p : ℕ} {M : Type} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (Fin p → ℂ) M] [IsManifold 𝓘(ℂ, Fin p → ℂ) 1 M]
    {U V : Opens M} (h : U ≤ V) :
    OpenEmbeddingExtension.Constructions.openEmbeddingCompactExtension (NestedOpenPointClass.Constructions.opensInclusionMap (X := TopCat.of M) h)
      (NestedOpenPointClass.Constructions.opensInclusionMap_isOpenEmbedding (X := TopCat.of M) h) (2*p) ≫
      AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace p (M := V) = AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace p (M := U) := by
  rw [← AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace_open p V, ← Category.assoc, openEmbeddingCompactExtension_nested,
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace_open]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NestedOpenTrace.Constructions
