import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionStableCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.IdealClosedFamilies
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.HomogeneousFamilyConstruction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.AffineCoordinateLift

/-! # Saturated Ideal Coordinate Lift -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A saturated flat Hilbert ideal over a noetherian coefficient ring
has an actual native projective family and a unique bounded Hilbert
parameter whose Grassmannian coordinates are precisely its degree
relations in the fixed monomial basis. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {C : Type u} [CommRing C] [IsNoetherianRing C] {n : ℕ} {P : Polynomial ℚ}
variable (I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal C n P) {S : Scheme.{u}} (f : Spec (.of C) ⟶ S)

def SaturatedFlatIdeals.SaturatedFlatHilbertIdeal.nativeHilbertFamily : HilbertScheme.Presentations.Hilbert.Functor.Family (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f) := by
  haveI : LocallyOfFinitePresentation (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I.ideal)) :=
    I.family_locallyFinitePresentation
  exact HilbertScheme.Presentations.Intrinsic.HomogeneousFamilyConstruction.GradedHilbert.nativeFamilyOfHomogeneousIdeal n f I.ideal

theorem SaturatedFlatIdeals.SaturatedFlatHilbertIdeal.nativeHilbertFamily_coordinates : HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f (I.nativeHilbertFamily f) = I.ideal := by
  have : LocallyOfFinitePresentation (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I.ideal)) :=
    I.family_locallyFinitePresentation
  exact (HilbertScheme.Presentations.Intrinsic.HomogeneousFamilyConstruction.GradedHilbert.nativeFamilyOfHomogeneousIdeal_coordinates n f I.ideal).trans
    (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation_eq_of_saturated I.ideal I.saturated)

theorem SaturatedFlatIdeals.SaturatedFlatHilbertIdeal.nativeHilbertFamily_residue_polynomial :
    ∀ p : PrimeSpectrum C, HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
      (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField)
        (HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f (I.nativeHilbertFamily f)))).toIdeal P := by
  rw [I.nativeHilbertFamily_coordinates f]
  exact I.hilbert

theorem SaturatedFlatIdeals.SaturatedFlatHilbertIdeal.nativeHilbertFamily_coordinatePoint (D : ℕ)
    (hdegree : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D) :
    HilbertScheme.Presentations.Intrinsic.AffineGrassmannian.GradedHilbert.nativeAffineCoordinateGrassmannian f (I.nativeHilbertFamily f) P
      (I.nativeHilbertFamily_residue_polynomial f) D hdegree
      (ULift.{u} (Fin (P.eval (D : ℚ)).num.toNat)) (by simp) =
        TorsionStableCoordinates.configurationHilbertCoordinatePoint I D hdegree := by
  apply Module.Grassmannian.ext
  change HilbertScheme.Presentations.DegreeCoordinateRelations.GradedHilbert.degreeCoordinateRelations (HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f (I.nativeHilbertFamily f)) D =
    HilbertScheme.Presentations.DegreeCoordinateRelations.GradedHilbert.degreeCoordinateRelations I.ideal D
  rw [I.nativeHilbertFamily_coordinates f]

theorem SaturatedFlatIdeals.SaturatedFlatHilbertIdeal.existsUnique_hilbert_coordinate_lift [IsLocallyNoetherian S] (D : ℕ)
    (hdegree : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D) :
    ∃! x : Over.mk f ⟶ HilbertScheme.Presentations.BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ULift.{u} (Fin (P.eval (D : ℚ)).num.toNat))
      n D S (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P),
      x ≫ HilbertScheme.Presentations.BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver n D S (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) =
        HilbertScheme.Presentations.Relative.AffineQuotientPoint.Grassmannian.relativeQuotientClassifyingPoint f (TorsionStableCoordinates.configurationHilbertCoordinatePoint I D hdegree) := by
  have h := HilbertScheme.Presentations.Noetherian.AffineCoordinateLift.GradedHilbert.existsUnique_noetherian_affine_hilbert_coordinate_lift
    (ι := ULift.{u} (Fin (P.eval (D : ℚ)).num.toNat)) f (I.nativeHilbertFamily f) P
    (I.nativeHilbertFamily_residue_polynomial f) hdegree (by simp)
  simp only [HilbertScheme.Presentations.Intrinsic.AffineGrassmannian.GradedHilbert.nativeAffineHilbertGrassmannianPoint, I.nativeHilbertFamily_coordinatePoint f D hdegree] at h
  have hdec :
      (fun a b : HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n D =>
        @ULift.instDecidableEq_mathlib (HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeMonomials n D)
          (fun a b => Subtype.instDecidableEq a b) a b) =
        (fun a b : HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n D =>
          @ULift.instDecidableEq_mathlib (HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeMonomials n D)
            (Homogeneous.Coordinates.homogeneousMonomials_decidableEq (Fin (n + 1)) D) a b) := Subsingleton.elim _ _
  rw [hdec] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
