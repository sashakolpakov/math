import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SaturatedIdealCoordinateLift
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.AffineClassification

/-! # Saturated Coordinate Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The bounded Hilbert parameter with the canonical coordinate
point of a saturated flat ideal pulls its universal family back to
the exact native embedded family of that ideal. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.AffineClassification.GradedHilbert
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {C : Type u} [CommRing C] [IsNoetherianRing C] {n : ℕ} {P : Polynomial ℚ}
variable (I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal C n P)
variable {S : Scheme.{u}} [IsLocallyNoetherian S] (f : Spec (.of C) ⟶ S)

theorem SaturatedFlatIdeals.SaturatedFlatHilbertIdeal.hilbert_coordinate_lift_family (D : ℕ) (hdegree : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)
    (x : Over.mk f ⟶ HilbertScheme.Presentations.BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ULift.{u} (Fin (P.eval (D : ℚ)).num.toNat))
      n D S (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P))
    (hx : x ≫ HilbertScheme.Presentations.BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver n D S (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) =
      HilbertScheme.Presentations.Relative.AffineQuotientPoint.Grassmannian.relativeQuotientClassifyingPoint f (TorsionStableCoordinates.configurationHilbertCoordinatePoint I D hdegree)) :
    HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
      (HilbertScheme.Presentations.BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily n D S (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P)) = I.nativeHilbertFamily f := by
  apply HilbertScheme.Presentations.Noetherian.AffineParameterFamily.GradedHilbert.noetherianAffine_hilbert_coordinate_lift_family f (I.nativeHilbertFamily f) P
    (I.nativeHilbertFamily_residue_polynomial f) hdegree (by simp) x
  have hdec :
      (fun a b : HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n D =>
        @ULift.instDecidableEq_mathlib (HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeMonomials n D)
          (fun a b => Subtype.instDecidableEq a b) a b) =
        (fun a b : HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n D =>
          @ULift.instDecidableEq_mathlib (HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert.DegreeMonomials n D)
            (Homogeneous.Coordinates.homogeneousMonomials_decidableEq (Fin (n + 1)) D) a b) := Subsingleton.elim _ _
  simp only [HilbertScheme.Presentations.Intrinsic.AffineGrassmannian.GradedHilbert.nativeAffineHilbertGrassmannianPoint, I.nativeHilbertFamily_coordinatePoint f D hdegree]
  rw [hdec]
  exact hx

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
