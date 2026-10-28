import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.LocusClassifiers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.ParameterIntersectionLifts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Bounded.PolarizedLevelIntersection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli.InclusionComposition

/-! # Inverse Classifier -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli

noncomputable section

/-! Every bounded complete moduli isomorphism lifts to a specified point of the combined parameter locus, preserving its ambient abelian classifier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} [IsNoetherian S] {g N n : ℕ} [NeZero N] {δ : Fin g → ℕ}
variable (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
variable (j : A.abelian.scheme ⊗ B.abelian.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left]
variable (P : Polynomial ℚ) (PB : Projective.ProjectivePresentations.ProjectivePresentation B.abelian.scheme)
variable {T : Over S} (e : IsomorphismFunctor.BoundedFamilyLevelIso A B j P T)

def IsomorphismFunctor.BoundedFamilyLevelIso.classifier : T ⟶ Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameter A B j P :=
  Closed.ParameterIntersectionLifts.closedParameterIntersectionLift (Bounded.PolarizationEqualityParameters.boundedPolarizationIsoParameterInclusion A.polarization B.polarization j P)
    (Bounded.LevelIsomorphismParameters.boundedFullLevelIsoParameterInclusion A.abelian B.abelian A.level B.level j P)
    (IsomorphismFunctor.BoundedFamilyLevelIso.polarizationClassifier A B j P PB e) (IsomorphismFunctor.BoundedFamilyLevelIso.fullLevelClassifier A B j P PB e)
    ((IsomorphismFunctor.BoundedFamilyLevelIso.polarizationClassifier_comp A B j P PB e).trans (IsomorphismFunctor.BoundedFamilyLevelIso.fullLevelClassifier_comp A B j P PB e).symm)

theorem IsomorphismFunctor.BoundedFamilyLevelIso.classifier_polarization :
    IsomorphismFunctor.BoundedFamilyLevelIso.classifier A B j P PB e ≫ Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameterToPolarization A B j P =
      IsomorphismFunctor.BoundedFamilyLevelIso.polarizationClassifier A B j P PB e :=
  Closed.ParameterIntersectionLifts.closedParameterIntersectionLift_fst
    (Bounded.PolarizationEqualityParameters.boundedPolarizationIsoParameterInclusion A.polarization B.polarization j P)
    (Bounded.LevelIsomorphismParameters.boundedFullLevelIsoParameterInclusion A.abelian B.abelian A.level B.level j P)
    (IsomorphismFunctor.BoundedFamilyLevelIso.polarizationClassifier A B j P PB e) (IsomorphismFunctor.BoundedFamilyLevelIso.fullLevelClassifier A B j P PB e)
    ((IsomorphismFunctor.BoundedFamilyLevelIso.polarizationClassifier_comp A B j P PB e).trans (IsomorphismFunctor.BoundedFamilyLevelIso.fullLevelClassifier_comp A B j P PB e).symm)

theorem IsomorphismFunctor.BoundedFamilyLevelIso.classifier_comp :
    IsomorphismFunctor.BoundedFamilyLevelIso.classifier A B j P PB e ≫ Bounded.PolarizedLevelIntersection.boundedPolarizedLevelIsoParameterInclusion A B j P = IsomorphismFunctor.BoundedFamilyLevelIso.abelianClassifier A B j P e := by
  exact (InclusionComposition.boundedPolarizedLevelIsoParameterInclusion_comp A B j P (IsomorphismFunctor.BoundedFamilyLevelIso.classifier A B j P PB e)).trans
    ((congrArg (fun z => z ≫ Bounded.PolarizationEqualityParameters.boundedPolarizationIsoParameterInclusion A.polarization B.polarization j P)
      (IsomorphismFunctor.BoundedFamilyLevelIso.classifier_polarization A B j P PB e)).trans
      (IsomorphismFunctor.BoundedFamilyLevelIso.polarizationClassifier_comp A B j P PB e))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BoundedModuli
