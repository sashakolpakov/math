import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.EvaluationBasisCoverage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.BasisCoordinateFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.GlobalSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.FramedEvaluationBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.FramedEvaluationComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.SectionBundleTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.CoefficientSectionBasis
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProperFlat.SectionFiberCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.NormalizedGraphPolynomial

/-! # Family Evaluation Matrix -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Matrices obtained by evaluating a geometrically complete graph-power
section family at the actual ordered torsion sections have projective
frames on every algebraically closed geometric fiber. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Scheme.{u}} {g N n : ℕ} {δ : Fin g → ℕ} [NeZero n]
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem PolarizationData.PolarizedAbelianWithFullLevel.fullLevelFamilyEvaluationMatrix_geometric_frame
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
    (level : A.abelian.FullLevel n)
    (hlarge : Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ * Uniform.GraphIntersectionData.graphTorsionHyperplaneDegree g δ < n ^ 2)
    (s : Fin (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ) →
      (Line.Bundles.structureModule A.abelian.scheme.left ⟶ A.uniformFrameLineBundle.sheaf))
    (hs : ProperFlat.SectionFiberCriterion.GeometricallyCompleteSectionFamily A.abelian.scheme.hom A.uniformFrameLineBundle.sheaf s (𝟙 S))
    (e : ∀ i : Fin (n ^ (2 * g)),
      (A.uniformFrameLineBundle.pullback (A.fullLevelSectionAtIndex level i)).sheaf ≅ Line.Bundles.structureModule S)
    (K : Type u) [Field K] [IsAlgClosed K] (q : Spec (.of K) ⟶ S) :
    Finite.IndexedProjectiveFrames.HasFiniteIndexedProjectiveFrame (K := K) (r := Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ)
      (fun i k => Geometric.FrameOpenCover.fieldPointGlobalScalarMap q (A.fullLevelFamilyEvaluationMatrix level s e i k)) := by
  obtain ⟨b, z, heq⟩ := A.fullLevelFamilyEvaluationMatrix_geometric_basis level s hs e K q
  rw [heq]
  exact ((A.pullback q).fullLevelBasisCoordinates_enumerated_haveFrame hg hδ hN
    (Geometric.NormalizedGraphPolynomial.fieldPoint_natCast_ne_zero_of_global_unit hunit q) (level.pullback q) hlarge b).units_smul z

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
