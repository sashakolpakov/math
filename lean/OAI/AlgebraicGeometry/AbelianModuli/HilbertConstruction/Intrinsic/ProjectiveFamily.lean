import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ProjectiveAmbient
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.PullbackRecoveryIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.FamilyBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.ParameterEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyTestPoints
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CanonicalFiberPolynomial

/-! # Projective Family -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ProjectiveFamily

noncomputable section

/-! Converting the native ideal-defined Hilbert family while retaining
its exact homogeneous ideal and its original family scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.CanonicalFiberPolynomial.GradedHilbert
universe u
variable {S : Scheme.{u}}

private theorem idealComapIso_composite_isIso {X Y : Scheme.{u}}
    (e : X ≅ Y) (I : Y.IdealSheafData) :
    IsIso ((I.comapIso e.hom).hom ≫ pullback.snd e.hom I.subschemeι) := by
  infer_instance

def nativeProjectiveClosedFamily (n : ℕ) (T : Over S)
    (F : HilbertScheme.Presentations.Hilbert.Functor.Family (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T) : Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver T.left n) :=
  (⟨F.val, F.property.1, F.property.2.2⟩ :
    Closed.Families.FlatClosedFamily (Over.mk (HilbertScheme.Presentations.Hilbert.Functor.ambientProjection (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T))).pullbackAlong
    (ProjectiveAmbient.nativeHilbertAmbientIso T n).hom (𝟙 T.left) (ProjectiveAmbient.nativeHilbertAmbientIso_isPullback T n)

theorem nativeProjectiveClosedFamily_ideal (n : ℕ) (T : Over S)
    (F : HilbertScheme.Presentations.Hilbert.Functor.Family (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T) :
    (nativeProjectiveClosedFamily n T F).ideal = F.val.comap (ProjectiveAmbient.nativeHilbertAmbientIso T n).hom := rfl

def nativeProjectiveClosedFamilyIso (n : ℕ) (T : Over S)
    (F : HilbertScheme.Presentations.Hilbert.Functor.Family (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T) :
    (nativeProjectiveClosedFamily n T F).scheme ≅ FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T F := by
  let g : (nativeProjectiveClosedFamily n T F).scheme.left ⟶
      (FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T F).left :=
    (F.val.comapIso (ProjectiveAmbient.nativeHilbertAmbientIso T n).hom).hom ≫
      pullback.snd (ProjectiveAmbient.nativeHilbertAmbientIso T n).hom F.val.subschemeι
  haveI : IsIso g := idealComapIso_composite_isIso (ProjectiveAmbient.nativeHilbertAmbientIso T n) F.val
  refine Over.isoMk (asIso g) ?_
  exact (ClosedFamily.Transport.closedFamilyTransport_isPullback
    (P := Over.mk (HilbertScheme.Presentations.Hilbert.Functor.ambientProjection (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T))
    (Q := Projective.ProjectivePresentations.projectiveSpaceOver T.left n) (ProjectiveAmbient.nativeHilbertAmbientIso T n).hom (𝟙 T.left)
    (ProjectiveAmbient.nativeHilbertAmbientIso_isPullback T n) F.val).w.trans (Category.comp_id _)

theorem nativeProjectiveClosedFamilyIso_embedding (n : ℕ) (T : Over S)
    (F : HilbertScheme.Presentations.Hilbert.Functor.Family (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T) :
    (nativeProjectiveClosedFamilyIso n T F).hom.left ≫ F.val.subschemeι =
      (nativeProjectiveClosedFamily n T F).ideal.subschemeι ≫ (ProjectiveAmbient.nativeHilbertAmbientIso T n).hom :=
  ClosedFamily.PullbackRecoveryIso.closedFamilyTransport_embedding F.val (ProjectiveAmbient.nativeHilbertAmbientIso T n).hom

theorem nativeProjectiveClosedFamily_affine_ideal (n : ℕ) (T : Over S)
    (F : HilbertScheme.Presentations.Hilbert.Functor.Family (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T) {R : Type u} [CommRing R]
    (a : Spec (.of R) ⟶ T.left) :
    ((nativeProjectiveClosedFamily n T F).affineProjectivePullback a).ideal =
      (HilbertScheme.Presentations.Affine.IntrinsicPolynomialFamily.GradedHilbert.affineNativeToPolynomial n (a ≫ T.hom)
        (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n)
          (Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T) F)).ideal := by
  change (F.val.comap (ProjectiveAmbient.nativeHilbertAmbientIso T n).hom).comap (AffineProjective.Charts.affineProjectiveChartMap a n) =
    (F.val.comap (HilbertScheme.Presentations.Hilbert.Functor.ambientMap (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n)
      (Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T))).comap (HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n (a ≫ T.hom)).hom
  exact (F.val.comap_comp (AffineProjective.Charts.affineProjectiveChartMap a n)
      (ProjectiveAmbient.nativeHilbertAmbientIso T n).hom).symm.trans
    ((congrArg (fun g => F.val.comap g) (ProjectiveAmbient.nativeHilbertAmbientIso_affine T n a)).trans
      (F.val.comap_comp (HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n (a ≫ T.hom)).hom
        (HilbertScheme.Presentations.Hilbert.Functor.ambientMap (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n)
          (Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T))))

theorem nativeProjectiveClosedFamily_affine_homogeneousIdeal (n : ℕ) (T : Over S)
    (F : HilbertScheme.Presentations.Hilbert.Functor.Family (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T) {R : Type u} [CommRing R]
    (a : Spec (.of R) ⟶ T.left) :
    ((nativeProjectiveClosedFamily n T F).affineProjectivePullback a).homogeneousIdeal =
      HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n (a ≫ T.hom)
        (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n)
          (Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T) F) := by
  exact congrArg HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf (nativeProjectiveClosedFamily_affine_ideal n T F a)

theorem nativeProjectiveClosedFamily_pullback (n : ℕ) {U T : Over S}
    (F : HilbertScheme.Presentations.Hilbert.Functor.Family (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T) (a : U ⟶ T) :
    nativeProjectiveClosedFamily n U (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) a F) =
      (nativeProjectiveClosedFamily n T F).projectiveBaseChange a.left := by
  apply Closed.Families.FlatClosedFamily.ext
  change (F.val.comap (HilbertScheme.Presentations.Hilbert.Functor.ambientMap (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) a)).comap
      (ProjectiveAmbient.nativeHilbertAmbientIso U n).hom =
    (F.val.comap (ProjectiveAmbient.nativeHilbertAmbientIso T n).hom).comap (RelativeProjective.BaseMaps.relativeProjectiveBaseMap a.left n)
  simpa only [Scheme.IdealSheafData.comap_comp] using
    congrArg (fun g => F.val.comap g) (ProjectiveAmbient.nativeHilbertAmbientIso_natural a n).symm

def nativeProjectiveHilbertFamily (n : ℕ) (T : Over S)
    (F : HilbertScheme.Presentations.Hilbert.Functor.Family (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T)
    (P : Polynomial ℚ) (hP : HilbertScheme.Presentations.CanonicalFiberPolynomial.GradedHilbert.CanonicalFiberHilbertPolynomial F P) :
    RelativeProjective.Families.RelativeProjectiveHilbertFamily T.left n P where
  family := nativeProjectiveClosedFamily n T F
  fieldHilbert K _ a := by
    rw [nativeProjectiveClosedFamily_affine_homogeneousIdeal]
    exact hP K a

theorem nativeProjectiveHilbertFamily_pullback (n : ℕ) {U T : Over S}
    (F : HilbertScheme.Presentations.Hilbert.Functor.Family (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T)
    (P : Polynomial ℚ) (hP : HilbertScheme.Presentations.CanonicalFiberPolynomial.GradedHilbert.CanonicalFiberHilbertPolynomial F P) (a : U ⟶ T) :
    nativeProjectiveHilbertFamily n U (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) a F)
        P (hP.pullback a) = (nativeProjectiveHilbertFamily n T F P hP).pullback a.left := by
  apply RelativeProjective.Families.RelativeProjectiveHilbertFamily.ext
  exact nativeProjectiveClosedFamily_pullback n F a

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ProjectiveFamily
