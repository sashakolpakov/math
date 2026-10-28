import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.HomogeneousCoordinateBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffineQuotientPoint

/-! # Over Coordinate Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.OverCoordinateBaseChange

noncomputable section

/-! Coefficient base change in homogeneous and Grassmannian coordinates
for arbitrary over-maps between affine test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace GradedHilbert

universe u
variable {A R : Type u} [CommRing A] [CommRing R] {S : Scheme.{u}} {n : ℕ}

theorem affineNativeHomogeneousIdeal_over_baseChange
    (f : Spec (.of A) ⟶ S) (g : Spec (.of R) ⟶ S)
    (b : Over.mk g ⟶ Over.mk f) (φ : A →+* R)
    (hb : Spec.map (CommRingCat.ofHom φ) = b.left)
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f)) :
    IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n g (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) b F) =
      Projective.Saturation.GradedHilbert.projectiveSaturation ((IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F).map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)) := by
  have hw : Spec.map (CommRingCat.ofHom φ) ≫ f = g := by rw [hb]; exact b.w
  have he : b = Over.homMk (Spec.map (CommRingCat.ofHom φ)) hw := Over.OverMorphism.ext hb.symm
  rw [he]
  exact Eq.rec (motive := fun (g' : Spec (.of R) ⟶ S) (h : Spec.map (CommRingCat.ofHom φ) ≫ f = g') =>
    IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n g' (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n)
      (Over.homMk (Spec.map (CommRingCat.ofHom φ)) h : Over.mk g' ⟶ Over.mk f) F) =
        Projective.Saturation.GradedHilbert.projectiveSaturation ((IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F).map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)))
      (HomogeneousCoordinateBaseChange.GradedHilbert.affineNativeHomogeneousIdeal_baseChange φ n f F) hw

end GradedHilbert

namespace Grassmannian

universe u
variable {A R : Type u} [CommRing A] [CommRing R] {S : Scheme.{u}}
variable {ι ν : Type u} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]

theorem relativeQuotientClassifyingPoint_over_natural
    (f : Spec (.of A) ⟶ S) (g : Spec (.of R) ⟶ S)
    (b : Over.mk g ⟶ Over.mk f) (φ : A →+* R)
    (hb : Spec.map (CommRingCat.ofHom φ) = b.left)
    (H : Module.Grassmannian A (ν → A) (Fintype.card ι)) :
    b ≫ Relative.AffineQuotientPoint.Grassmannian.relativeQuotientClassifyingPoint f H =
      Relative.AffineQuotientPoint.Grassmannian.relativeQuotientClassifyingPoint g (Coordinate.GrassmannianBaseChange.Grassmannian.coordinateGrassmannianMap φ H) := by
  have hw : Spec.map (CommRingCat.ofHom φ) ≫ f = g := by rw [hb]; exact b.w
  apply Over.OverMorphism.ext
  change b.left ≫ (QuotientClassifyingMap.Grassmannian.quotientClassifyingMap (.of A) H ≫ Presentations.Grassmannian.BaseMap.grassmannianBaseMap f) =
    QuotientClassifyingMap.Grassmannian.quotientClassifyingMap (.of R) (Coordinate.GrassmannianBaseChange.Grassmannian.coordinateGrassmannianMap φ H) ≫ Presentations.Grassmannian.BaseMap.grassmannianBaseMap g
  rw [← hb, ← hw, Presentations.Grassmannian.BaseMap.grassmannianBaseMap_comp]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ Presentations.Grassmannian.BaseMap.grassmannianBaseMap f)
      (Quotient.ClassifyingNaturality.Grassmannian.quotientClassifyingMap_natural (.of A) (.of R) φ H).symm).trans (Category.assoc _ _ _))

end Grassmannian

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.OverCoordinateBaseChange
