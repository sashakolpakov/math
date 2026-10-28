import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.CoordinateBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.ClosedFamilies
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.QuotientRankBaseChange

/-! # Recovered Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The uniform high-degree coordinates of a noetherian Hilbert model recover finite projective coordinates of the actual family after arbitrary coefficient extension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.QuotientRankBaseChange.GradedHilbert

universe u

theorem Closed.Families.FlatClosedFamily.exists_homogeneousQuotient_of_noetherian_model
    {C R : CommRingCat.{u}} [IsNoetherianRing C] (φ : C ⟶ R)
    {n : ℕ} {P : Polynomial ℚ} (G : HilbertConstruction.Flat.ClosedFamilies.FlatClosedHilbertFamily C n P)
    (F : Closed.Families.FlatClosedFamily (HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R n))
    (hF : F = G.val.pullbackAlong (HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n) (Spec.map φ)
      (HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap_isPullback φ n))
    (d : ℕ) (hd : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ d) :
    ∃ Q : Module.Grassmannian R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d) (P.eval (d : ℚ)).num.toNat,
      Q.toSubmodule = HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations F.homogeneousIdeal.toIdeal d := by
  let : Algebra C R := φ.hom.toAlgebra
  let I := G.val.homogeneousIdeal
  have : Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) := G.val.homogeneousIdeal_flat
  have hSat : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal := G.val.homogeneousIdeal_saturated
  have hdeg : HilbertScheme.Presentations.RegularCoordinateFlag.GradedHilbert.regularCoordinateFlagBound.{u} n P ≤ d := (le_max_left _ _).trans hd
  have : Module.Projective C (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) :=
    HilbertScheme.Presentations.Uniform.SaturatedCoordinates.GradedHilbert.uniform_saturated_coordinate_projective I hSat P G.property d hdeg
  obtain ⟨hproj, hsat⟩ := HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniform_saturated_coordinate_all_baseChanges I hSat P G.property R d hdeg
  have : Module.Projective R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := R) I).toIdeal d) := hproj
  have he : F.homogeneousIdeal = HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := R) I) :=
    (congrArg Closed.Families.FlatClosedFamily.homogeneousIdeal hF).trans (G.val.homogeneousIdeal_coefficientBaseChange φ)
  let Q : Module.Grassmannian R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d) (P.eval (d : ℚ)).num.toNat :=
    { toSubmodule := HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := R) I).toIdeal d
      finite_quotient := HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeQuotient_finite _ _
      projective_quotient := inferInstance
      rankAtStalk_eq := fun q =>
        (HilbertScheme.Presentations.QuotientRankBaseChange.GradedHilbert.degreeQuotient_rankAtStalk_baseChange (A := R) I d q).trans
          (HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree_rankAtStalk I hSat P G.property d hd _) }
  refine ⟨Q, ?_⟩
  change HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := R) I).toIdeal d = _
  rw [he, hsat]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
