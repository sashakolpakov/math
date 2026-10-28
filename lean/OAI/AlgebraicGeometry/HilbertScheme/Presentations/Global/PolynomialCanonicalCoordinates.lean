import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.PointComposition
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.Polynomial

/-! # Polynomial Canonical Coordinates -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.PolynomialCanonicalCoordinates.GradedHilbert

noncomputable section

/-! The canonical homogeneous coordinates of an actual polynomial point
family are the saturation of its coefficient-specialized ideal. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (M : Over S) {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n))
variable {R : Type u} [CommRing R] (a : Spec (.of R) ⟶ M.left)
variable (f : Spec (.of R) ⟶ S) (ha : a ≫ M.hom = f)

theorem globalPolynomialPointPresentation_inclusion :
    (ProjectivePoint.GradedHilbert.globalPolynomialPointPresentation M n a I f ha).hom ≫
        PolynomialInclusion.GradedHilbert.globalPolynomialInclusion M I (ProjectivePoint.GradedHilbert.polynomialPointMorphismOver M a f ha) =
      Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (Projective.QuotientPoint.GradedHilbert.pointHomogeneousIdeal M I a) ≫ (Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n f).hom := by
  apply (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd (Over.mk f) (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n))).hom_ext
  · change (_ ≫ _) ≫ Hilbert.Functor.ambientProjection (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f) =
      (_ ≫ _) ≫ Hilbert.Functor.ambientProjection (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f)
    rw [Category.assoc, PolynomialInclusion.GradedHilbert.globalPolynomialInclusion_projection, Category.assoc, Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso_projection]
    exact (Projective.QuotientPoint.GradedHilbert.projectiveQuotientPointIso_projection M I a).trans
      (Projective.QuotientStructure.GradedHilbert.projectiveQuotientInclusion_structure (Projective.QuotientPoint.GradedHilbert.pointHomogeneousIdeal M I a)).symm
  · change (_ ≫ _) ≫ (prod.snd : Over.mk f ⨯ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n ⟶ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n).left =
      (_ ≫ _) ≫ (prod.snd : Over.mk f ⨯ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n ⟶ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n).left
    rw [Category.assoc, ProjectivePoint.GradedHilbert.projectiveQuotientPointIso_global_projective,
      Category.assoc, Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso_projective, Projective.PointComposition.GradedHilbert.globalProjectiveSchemePointMap_eq, ha]

theorem globalPolynomialPoint_kernel :
    (PolynomialInclusion.GradedHilbert.globalPolynomialInclusion M I (ProjectivePoint.GradedHilbert.polynomialPointMorphismOver M a f ha)).ker =
      (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (Projective.QuotientPoint.GradedHilbert.pointHomogeneousIdeal M I a)).ker.comap (Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n f).inv := by
  have h := congrArg Scheme.Hom.ker (globalPolynomialPointPresentation_inclusion M I a f ha)
  rw [Scheme.Hom.ker_comp_of_isIso, PolynomialInclusion.closedImmersion_comp_iso_ker] at h
  exact h

theorem globalPolynomialFamily_canonical_coordinates
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f))
    (hF : F.val = (PolynomialInclusion.GradedHilbert.globalPolynomialInclusion M I (ProjectivePoint.GradedHilbert.polynomialPointMorphismOver M a f ha)).ker) :
    Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F = Projective.Saturation.GradedHilbert.projectiveSaturation (Projective.QuotientPoint.GradedHilbert.pointHomogeneousIdeal M I a) := by
  change ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf (F.val.comap (Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n f).hom) = _
  rw [hF, globalPolynomialPoint_kernel, ← Scheme.IdealSheafData.comap_comp,
    Iso.hom_inv_id, Scheme.IdealSheafData.comap_id]
  rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.PolynomialCanonicalCoordinates.GradedHilbert
