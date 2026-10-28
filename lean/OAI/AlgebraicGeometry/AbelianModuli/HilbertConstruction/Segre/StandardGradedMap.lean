import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReindexedSegreEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SegreOver

/-! # Standard Graded Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.StandardGradedMap

noncomputable section

/-! The Segre inclusion followed by the actual finite-coordinate
reindexing is one explicit graded projective morphism. Its variable images
are the genuine quotient matrix entries. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
universe u
variable (R : Type u) [CommRing R] {n m d : ℕ}
variable (e : ChartProjections.SegreProjectiveIndex.{u} n m ≃ Fin (d + 1))

def segreStandardGradedMap : Projective.ProjectivePresentations.coordinateGrading R d →+*ᵍ ChartCoordinates.segreQuotientGrading (σ := ULift.{u} (Fin (n + 1)))
    (τ := ULift.{u} (Fin (m + 1))) R :=
  (HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap (HomogeneousRelations.segreHomogeneousIdeal R)).comp (Polynomial.Reindex.polynomialReindexGraded R e.symm)

theorem segreStandardGradedMap_variable (i : Fin (d + 1)) :
    segreStandardGradedMap R e (X i) = (ChartCoordinates.segreVariable R (e.symm i)).val := by
  change HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap (HomogeneousRelations.segreHomogeneousIdeal R) (MvPolynomial.rename e.symm (X i)) =
    HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap (HomogeneousRelations.segreHomogeneousIdeal R) (X (e.symm i))
  exact congrArg (HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap (HomogeneousRelations.segreHomogeneousIdeal R)) (MvPolynomial.rename_X e.symm i)

theorem segreStandardGradedMap_irrelevant :
    HomogeneousIdeal.irrelevant (ChartCoordinates.segreQuotientGrading (σ := ULift.{u} (Fin (n + 1)))
      (τ := ULift.{u} (Fin (m + 1))) R) ≤
    (HomogeneousIdeal.irrelevant (Projective.ProjectivePresentations.coordinateGrading R d)).map (segreStandardGradedMap R e) :=
  HomogeneousIdeal.irrelevant_le_map_comp
    (Polynomial.Reindex.polynomialReindexGraded_irrelevant R e.symm) (HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.irrelevant_quotient_le_map (HomogeneousRelations.segreHomogeneousIdeal R))

theorem segreStandardGradedMap_proj :
    Proj.map (segreStandardGradedMap R e) (segreStandardGradedMap_irrelevant R e) =
      ProjectiveScheme.segreProjectiveInclusion (CommRingCat.of R) ≫ (Projective.SpaceReindex.affineProjectiveSpaceReindexIso R e).hom.left := by
  change Proj.map ((HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap (HomogeneousRelations.segreHomogeneousIdeal R)).comp
      (Polynomial.Reindex.polynomialReindexGraded R e.symm)) _ =
    Proj.map (HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap (HomogeneousRelations.segreHomogeneousIdeal R)) _ ≫
      Proj.map (Polynomial.Reindex.polynomialReindexGraded R e.symm) _
  exact Proj.map_comp _ _ _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.StandardGradedMap
