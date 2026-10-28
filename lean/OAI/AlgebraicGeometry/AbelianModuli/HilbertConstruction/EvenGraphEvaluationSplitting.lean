import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphFamilyEvaluationMatrix
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GeometricMatrixSplitting

/-! # Even Graph Evaluation Splitting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! On an affine base, sufficiently high torsion evaluation of a
geometrically complete section family has a left inverse. Its matrix
therefore remains injective after every coefficient change. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical
universe u
variable {R : Type u} [CommRing R] {g N n r : ℕ} {δ : Fin g → ℕ} [NeZero n]
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of R)))
variable (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N)
variable (hunit : IsUnit (N : Γ(Spec (.of R), ⊤)))
variable (level : A.abelian.FullLevel n) (t : ℕ) (ht : 0 < t)
variable (htlarge : Graph.EmbeddingNumerics.graphSquareSectionRank g δ ≤ t)
variable (hlarge : EvenGraphTorsionBound.evenGraphTorsionDegree g δ t < n ^ 2)
variable (s : Fin r → (Line.Bundles.structureModule A.abelian.scheme.left ⟶
  (A.graphBundle.tensorPower (2 * t)).sheaf))
variable (hs : ProperFlat.SectionFiberCriterion.GeometricallyCompleteSectionFamily A.abelian.scheme.hom
  (A.graphBundle.tensorPower (2 * t)).sheaf s (𝟙 (Spec (.of R))))
variable (e : ∀ c : Multiplicative (Fin (2 * g) → ZMod n),
  ((A.graphBundle.tensorPower (2 * t)).pullback (A.abelian.fullLevelGlobalSection level c)).sheaf ≅
    Line.Bundles.structureModule (Spec (.of R)))

include hg hδ hN hunit ht htlarge hlarge hs

theorem PolarizationData.PolarizedAbelianWithFullLevel.evenGraphFamilyEvaluationMatrix_leftInverse :
    ∃ B : Matrix (Fin r) (Multiplicative (Fin (2 * g) → ZMod n)) R,
      B * Affine.GeometricMatrixSplitting.affineCoordinateMatrix (A.evenGraphFamilyEvaluationMatrix level t s e) = 1 :=
  Affine.GeometricMatrixSplitting.affineCoordinateMatrix_leftInverse _
    (A.evenGraphFamilyEvaluationMatrix_geometric_injective hg hδ hN hunit
      level t ht htlarge hlarge s hs e)

theorem PolarizationData.PolarizedAbelianWithFullLevel.evenGraphFamilyEvaluationMatrix_injective_all_baseChanges
    {C : Type u} [CommRing C] (φ : R →+* C) :
    Function.Injective (Matrix.toLin'
      ((Affine.GeometricMatrixSplitting.affineCoordinateMatrix (A.evenGraphFamilyEvaluationMatrix level t s e)).map φ)) :=
  Affine.GeometricMatrixSplitting.affineCoordinateMatrix_injective_all_baseChanges φ _
    (A.evenGraphFamilyEvaluationMatrix_geometric_injective hg hδ hN hunit
      level t ht htlarge hlarge s hs e)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
