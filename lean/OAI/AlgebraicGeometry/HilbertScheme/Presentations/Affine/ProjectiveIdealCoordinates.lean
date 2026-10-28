import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.IdealOrder
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.HomogeneousCoordinateBaseChange

/-! # Projective Ideal Coordinates -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ProjectiveIdealCoordinates

noncomputable section

/-! Canonical homogeneous coordinates for arbitrary native projective
ideal sheaves, without flatness assumptions on the closed ambient ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem ideal_comap_iso_le_iff {X Y : Scheme.{u}} (e : X ≅ Y) (I J : Y.IdealSheafData) :
    I.comap e.hom ≤ J.comap e.hom ↔ I ≤ J := by
  constructor
  · intro h
    have he := Scheme.IdealSheafData.comap_mono e.inv h
    simpa only [← Scheme.IdealSheafData.comap_comp, Iso.inv_hom_id,
      Scheme.IdealSheafData.comap_id] using he
  · intro h
    exact Scheme.IdealSheafData.comap_mono e.hom h

namespace GradedHilbert

variable {S : Scheme.{u}} (n : ℕ) {R A : Type u} [CommRing R] [CommRing A]
variable (a : Spec (CommRingCat.of R) ⟶ S)

def affineProjectiveIdealCoordinates
    (I : (Hilbert.Functor.ambient (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a)).IdealSheafData) :
    HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n) :=
  ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf (I.comap (ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a).hom)

theorem affineProjectiveIdealCoordinates_kernel
    (I : (Hilbert.Functor.ambient (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a)).IdealSheafData) :
    (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (affineProjectiveIdealCoordinates n a I)).ker =
      I.comap (ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a).hom :=
  Projective.IdealEquivalence.GradedHilbert.projectiveQuotient_homogeneousIdealOfSheaf _

theorem affineProjectiveIdealCoordinates_le_iff
    (I J : (Hilbert.Functor.ambient (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a)).IdealSheafData) :
    affineProjectiveIdealCoordinates n a I ≤ affineProjectiveIdealCoordinates n a J ↔ I ≤ J := by
  have h : (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (affineProjectiveIdealCoordinates n a I)).ker ≤
      (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (affineProjectiveIdealCoordinates n a J)).ker ↔
      affineProjectiveIdealCoordinates n a I ≤ affineProjectiveIdealCoordinates n a J := by
    have hi : Projective.Saturation.GradedHilbert.projectiveSaturation (affineProjectiveIdealCoordinates n a I) =
        affineProjectiveIdealCoordinates n a I :=
      Projective.Saturation.GradedHilbert.projectiveSaturation_eq_of_saturated _ (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf_saturated _)
    have hj : Projective.Saturation.GradedHilbert.projectiveSaturation (affineProjectiveIdealCoordinates n a J) =
        affineProjectiveIdealCoordinates n a J :=
      Projective.Saturation.GradedHilbert.projectiveSaturation_eq_of_saturated _ (ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf_saturated _)
    exact (Projective.IdealOrder.GradedHilbert.projectiveQuotientIdeal_le_iff (affineProjectiveIdealCoordinates n a I)
      (affineProjectiveIdealCoordinates n a J)).trans (by rw [hi, hj])
  exact h.symm.trans (by
    rw [affineProjectiveIdealCoordinates_kernel, affineProjectiveIdealCoordinates_kernel]
    exact ideal_comap_iso_le_iff (ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a) I J)

theorem affineProjectiveIdealCoordinates_baseChange (φ : R →+* A)
    (I : (Hilbert.Functor.ambient (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a)).IdealSheafData) :
    affineProjectiveIdealCoordinates n (Spec.map (CommRingCat.ofHom φ) ≫ a)
      (I.comap (Hilbert.Functor.ambientMap (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (ProjectiveAmbientNaturality.GradedHilbert.affineTestMap a φ))) =
    Projective.Saturation.GradedHilbert.projectiveSaturation ((affineProjectiveIdealCoordinates n a I).map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)) := by
  unfold Projective.Saturation.GradedHilbert.projectiveSaturation
  rw [HomogeneousCoordinateBaseChange.GradedHilbert.projectiveQuotientInclusion_coefficient_ker, affineProjectiveIdealCoordinates_kernel]
  unfold affineProjectiveIdealCoordinates
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    ProjectiveAmbientNaturality.GradedHilbert.affineProjectiveAmbientIso_naturality]

end GradedHilbert

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ProjectiveIdealCoordinates
