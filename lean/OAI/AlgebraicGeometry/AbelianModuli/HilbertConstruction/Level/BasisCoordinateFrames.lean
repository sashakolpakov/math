import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.LabelEnumeration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.FiniteIndexedFrame
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.IndexedFrameTransport

/-! # Basis Coordinate Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every complete basis of the uniform graph-power sections gives a
torsion point coordinate configuration containing a projective frame.
The labels can then be enumerated by their fixed cardinality n^(2g). -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] {g N n : ℕ} {δ : Fin g → ℕ} [NeZero n]
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem PolarizationData.PolarizedAbelianWithFullLevel.fullLevelBasisCoordinates_haveFrame
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    (level : A.abelian.FullLevel n)
    (hlarge : Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ * Uniform.GraphIntersectionData.graphTorsionHyperplaneDegree g δ < n ^ 2)
    (b : Module.Basis (Fin (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ)) K
      ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj
        (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf)) :
    Finite.IndexedProjectiveFrames.HasFiniteIndexedProjectiveFrame (K := K) (r := Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ)
      (fun i k => A.fullLevelSectionEvaluation level i (b k)) := by
  have h := (A.fullLevelSectionEvaluation_finiteIndexedFrame hg hδ hN hNk level hlarge).map
    b.dualBasis.equivFun
  have he : (fun i => b.dualBasis.equivFun (A.fullLevelSectionEvaluation level i)) =
      (fun i k => A.fullLevelSectionEvaluation level i (b k)) := by
    funext i k
    exact b.dualBasis_equivFun _ k
  exact he ▸ h

theorem PolarizationData.PolarizedAbelianWithFullLevel.fullLevelBasisCoordinates_enumerated_haveFrame
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    (level : A.abelian.FullLevel n)
    (hlarge : Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ * Uniform.GraphIntersectionData.graphTorsionHyperplaneDegree g δ < n ^ 2)
    (b : Module.Basis (Fin (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ)) K
      ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj
        (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf)) :
    Finite.IndexedProjectiveFrames.HasFiniteIndexedProjectiveFrame (K := K) (r := Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ)
      (fun i k => A.fullLevelSectionEvaluation level (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := n) i) (b k)) :=
  (A.fullLevelBasisCoordinates_haveFrame hg hδ hN hNk level hlarge b).reindex PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
