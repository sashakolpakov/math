import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.EvaluationBasisCoverage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.FamilyEvaluationData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.FramedEvaluationComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.SectionBundleTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.CoefficientSectionBasis
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.SectionFiberCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.NormalizedGraphPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FieldEvaluationCoverage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FrameCoverage

/-! # Evaluation Coverage -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Actual torsion evaluation matrices of complete graph embeddings
satisfy the stable chart inequalities on every geometric fiber. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped Classical
universe u
variable {S : Scheme.{u}} {g N n : ℕ} {δ : Fin g → ℕ} [NeZero n]
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem PolarizationData.PolarizedAbelianWithFullLevel.fullLevelFamilyEvaluationMatrix_geometric_stable
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
    (level : A.abelian.FullLevel n)
    (hlarge : Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ * Uniform.GraphIntersectionData.graphTorsionHyperplaneDegree g δ < n ^ 2)
    (s : Fin (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ) →
      (Line.Bundles.structureModule A.abelian.scheme.left ⟶ A.uniformFrameLineBundle.sheaf))
    (hs : ProperFlat.SectionFiberCriterion.GeometricallyCompleteSectionFamily A.abelian.scheme.hom A.uniformFrameLineBundle.sheaf s (𝟙 S))
    (e : ∀ i : Fin (n ^ (2 * g)),
      (A.uniformFrameLineBundle.pullback (A.fullLevelSectionAtIndex level i)).sheaf ≅ Line.Bundles.structureModule S)
    (K : Type u) [Field K] [IsAlgClosed K] (q : Spec (.of K) ⟶ S) :
    (∀ i, (fun k => Geometric.FrameOpenCover.fieldPointGlobalScalarMap q
      (A.fullLevelFamilyEvaluationMatrix level s e i k)) ≠ 0) ∧
    (∀ U : Submodule K (Fin (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ) → K), U ≠ ⊤ →
      Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ * (Finset.univ.filter (fun i =>
        (fun k => Geometric.FrameOpenCover.fieldPointGlobalScalarMap q (A.fullLevelFamilyEvaluationMatrix level s e i k)) ∈ U)).card <
          n ^ (2 * g)) := by
  obtain ⟨b, z, heq⟩ := A.fullLevelFamilyEvaluationMatrix_geometric_basis level s hs e K q
  let B := A.pullback q
  have hNk : (N : K) ≠ 0 := Geometric.NormalizedGraphPolynomial.fieldPoint_natCast_ne_zero_of_global_unit hunit q
  constructor
  · intro i
    have hi : (fun k => B.fullLevelSectionEvaluation (level.pullback q)
        (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration i) (b k)) ≠ 0 := by
      intro h
      apply B.fullLevelSectionEvaluation_ne_zero hδ hN hNk (level.pullback q) _
      apply b.ext
      intro k
      exact congrFun h k
    rw [show (fun k => Geometric.FrameOpenCover.fieldPointGlobalScalarMap q
        (A.fullLevelFamilyEvaluationMatrix level s e i k)) =
        (z i : K) • (fun k => B.fullLevelSectionEvaluation (level.pullback q)
          (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration i) (b k)) from congrFun heq i]
    exact smul_ne_zero (Units.ne_zero _) hi
  · intro U hU
    have hsparse := B.fullLevelBasisCoordinates_enumerated_sparse hg hδ hN hNk
      (level.pullback q) hlarge b
    have hscaled : Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ *
        (Finset.univ.filter (fun i => (z i : K) • (fun k =>
          B.fullLevelSectionEvaluation (level.pullback q) (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration i) (b k)) ∈ U)).card <
        n ^ (2 * g) := by
      simpa only [Fintype.card_fin] using
        StableHilbert.SparseCoverage.StableHilbertCoverage.sparse_units_smul (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ) _
          (fun W hW => by simpa only [Fintype.card_fin] using hsparse W hW) z U hU
    exact (congrArg (fun w : Fin (n ^ (2 * g)) → Fin (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ) → K =>
      Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ * (Finset.univ.filter (fun i => w i ∈ U)).card < n ^ (2 * g))
      heq).mpr hscaled

theorem PolarizationData.PolarizedAbelianWithFullLevel.uniformSectionMatrix_geometric_stable
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
    (level : A.abelian.FullLevel n)
    (hlarge : Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ * Uniform.GraphIntersectionData.graphTorsionHyperplaneDegree g δ < n ^ 2)
    {r : ℕ} (hr : r = Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ)
    (s : Fin r → (Line.Bundles.structureModule A.abelian.scheme.left ⟶ A.uniformFrameLineBundle.sheaf))
    (hs : ProperFlat.SectionFiberCriterion.GeometricallyCompleteSectionFamily A.abelian.scheme.hom A.uniformFrameLineBundle.sheaf s (𝟙 S))
    (e : ∀ i : Fin (n ^ (2 * g)),
      (A.uniformFrameLineBundle.pullback (A.fullLevelSectionAtIndex level i)).sheaf ≅ Line.Bundles.structureModule S)
    (K : Type u) [Field K] [IsAlgClosed K] (q : Spec (.of K) ⟶ S) :
    (∀ i, (fun k => Geometric.FrameOpenCover.fieldPointGlobalScalarMap q
      (Family.FramedSectionEvaluation.familyFramedSectionValue A.uniformFrameLineBundle
        (A.fullLevelSectionAtIndex level i) (e i) (s k))) ≠ 0) ∧
    (∀ U : Submodule K (Fin r → K), U ≠ ⊤ →
      r * (Finset.univ.filter (fun i => (fun k => Geometric.FrameOpenCover.fieldPointGlobalScalarMap q
        (Family.FramedSectionEvaluation.familyFramedSectionValue A.uniformFrameLineBundle
          (A.fullLevelSectionAtIndex level i) (e i) (s k))) ∈ U)).card < n ^ (2 * g)) := by
  subst r
  exact A.fullLevelFamilyEvaluationMatrix_geometric_stable hg hδ hN hunit level hlarge s hs e K q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
