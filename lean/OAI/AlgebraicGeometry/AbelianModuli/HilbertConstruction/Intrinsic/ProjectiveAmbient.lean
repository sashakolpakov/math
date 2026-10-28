import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceReindex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.BaseMaps
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ProjectiveAmbient
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.PointComposition
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.AmbientProjections

/-! # Projective Ambient -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ProjectiveAmbient

noncomputable section

/-! Comparison of the two actual projective ambients, with their original
coefficient projections and arbitrary-base maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem affineProjectiveSpace_hom_eq_native (R : Type u) [CommRing R] (n : ℕ) :
    (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom = HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) := by
  change Proj.toSpecZero (Projective.ProjectivePresentations.coordinateGrading R n) ≫
    Spec.map (CommRingCat.ofHom (Projective.ProjectivePresentations.degreeZeroConstants R n).toRingHom) = _
  rw [Projective.SpaceReindex.degreeZeroConstants_eq_algebraMap]
  rfl

theorem polynomialProjectiveMap_eq_native {R A : CommRingCat.{u}} (φ : R ⟶ A) (n : ℕ) :
    Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n =
      HilbertScheme.Presentations.Polynomial.ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap (n := n) φ.hom := rfl

theorem nativeProjectiveSpaceSquare (T : Scheme.{u}) (n : ℕ) :
    IsPullback (RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection T n) (Projective.ProjectivePresentations.projectiveSpaceOver T n).hom
      (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading Γ(T, ⊤) n)) T.toSpecΓ := by
  simpa only [affineProjectiveSpace_hom_eq_native] using
    (RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection_isPullback T n)

def nativeProjectiveSpaceIso (T : Scheme.{u}) (n : ℕ) :
    Projective.ProjectivePresentations.projectiveSpaceOver T n ≅ HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver T n :=
  Over.isoMk (nativeProjectiveSpaceSquare T n).isoPullback
    (nativeProjectiveSpaceSquare T n).isoPullback_hom_snd

theorem nativeProjectiveSpaceIso_coefficient (T : Scheme.{u}) (n : ℕ) :
    (nativeProjectiveSpaceIso T n).hom.left ≫
      pullback.fst (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading Γ(T, ⊤) n)) T.toSpecΓ =
        RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection T n :=
  (nativeProjectiveSpaceSquare T n).isoPullback_hom_fst

theorem nativeProjectiveSpaceIso_projection (T : Scheme.{u}) (n : ℕ) :
    (nativeProjectiveSpaceIso T n).hom.left ≫ (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver T n).hom =
      (Projective.ProjectivePresentations.projectiveSpaceOver T n).hom := (nativeProjectiveSpaceIso T n).hom.w

theorem nativeProjectiveSpaceIso_affine (T : Scheme.{u}) (n : ℕ) {R : Type u} [CommRing R]
    (a : Spec (.of R) ⟶ T) :
    AffineProjective.Charts.affineProjectiveChartMap a n ≫ (nativeProjectiveSpaceIso T n).hom.left = HilbertScheme.Presentations.Projective.Point.GradedHilbert.projectiveSchemePointMap n a := by
  apply pullback.hom_ext
  · have hpoly : Projective.CoefficientFunctoriality.polynomialProjectiveMap (AffineProjective.Charts.affinePointCoefficients a) n =
        HilbertScheme.Presentations.Polynomial.ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap
          (n := n) (HilbertScheme.Presentations.PointCoefficients.schemePointCoefficientMap a) :=
      polynomialProjectiveMap_eq_native (AffineProjective.Charts.affinePointCoefficients a) n
    exact (Category.assoc (AffineProjective.Charts.affineProjectiveChartMap a n) (nativeProjectiveSpaceIso T n).hom.left
        (pullback.fst (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading Γ(T, ⊤) n)) T.toSpecΓ)).trans
      ((congrArg (fun q => AffineProjective.Charts.affineProjectiveChartMap a n ≫ q)
          (nativeProjectiveSpaceIso_coefficient T n)).trans
        ((RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection_affine a n).trans
          (hpoly.trans (HilbertScheme.Presentations.Projective.Point.GradedHilbert.projectiveSchemePointMap_coefficient n a).symm)))
  · exact (Category.assoc (AffineProjective.Charts.affineProjectiveChartMap a n)
        (nativeProjectiveSpaceIso T n).hom.left (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver T n).hom).trans
      ((congrArg (fun q => AffineProjective.Charts.affineProjectiveChartMap a n ≫ q)
          (nativeProjectiveSpaceIso_projection T n)).trans
        ((AffineProjective.Charts.affineProjectiveChartMap_over a n).trans
          ((congrArg (fun q => q ≫ a) (affineProjectiveSpace_hom_eq_native R n)).trans
            (HilbertScheme.Presentations.Projective.Point.GradedHilbert.projectiveSchemePointMap_projection n a).symm)))

theorem nativeProjectiveSpaceIso_natural {U T : Scheme.{u}} (a : U ⟶ T) (n : ℕ) :
    RelativeProjective.BaseMaps.relativeProjectiveBaseMap a n ≫ (nativeProjectiveSpaceIso T n).hom.left =
      (nativeProjectiveSpaceIso U n).hom.left ≫ HilbertScheme.Presentations.Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap a n := by
  apply pullback.hom_ext
  · let cT : (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver T n).left ⟶ Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading Γ(T, ⊤) n) :=
      pullback.fst (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading Γ(T, ⊤) n)) T.toSpecΓ
    let cU : (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver U n).left ⟶ Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading Γ(U, ⊤) n) :=
      pullback.fst (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading Γ(U, ⊤) n)) U.toSpecΓ
    let q : Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading Γ(U, ⊤) n) ⟶ Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading Γ(T, ⊤) n) :=
      HilbertScheme.Presentations.Polynomial.ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap (n := n) a.appTop.hom
    have hL : (RelativeProjective.BaseMaps.relativeProjectiveBaseMap a n ≫ (nativeProjectiveSpaceIso T n).hom.left) ≫ cT =
        RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection U n ≫ q :=
      (Category.assoc _ _ cT).trans
        ((congrArg (fun z => RelativeProjective.BaseMaps.relativeProjectiveBaseMap a n ≫ z)
            (nativeProjectiveSpaceIso_coefficient T n)).trans
          ((RelativeProjective.BaseMaps.relativeProjectiveBaseMap_fst a n).trans
            (congrArg (fun z => RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection U n ≫ z)
              (polynomialProjectiveMap_eq_native a.appTop n))))
    have hR : ((nativeProjectiveSpaceIso U n).hom.left ≫
        HilbertScheme.Presentations.Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap a n) ≫ cT =
        RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection U n ≫ q :=
      (Category.assoc _ _ cT).trans
        ((congrArg (fun z => (nativeProjectiveSpaceIso U n).hom.left ≫ z)
            (HilbertScheme.Presentations.Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap_coefficient a n)).trans
          ((Category.assoc (nativeProjectiveSpaceIso U n).hom.left cU q).symm.trans
            (congrArg (fun z => z ≫ q) (nativeProjectiveSpaceIso_coefficient U n))))
    exact hL.trans hR.symm
  · change (RelativeProjective.BaseMaps.relativeProjectiveBaseMap a n ≫ (nativeProjectiveSpaceIso T n).hom.left) ≫
        (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver T n).hom =
      ((nativeProjectiveSpaceIso U n).hom.left ≫ HilbertScheme.Presentations.Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap a n) ≫
        (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver T n).hom
    rw [Category.assoc, nativeProjectiveSpaceIso_projection, RelativeProjective.BaseMaps.relativeProjectiveBaseMap_over,
      Category.assoc, HilbertScheme.Presentations.Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap_projection,
      ← Category.assoc, nativeProjectiveSpaceIso_projection]

variable {S : Scheme.{u}}

def nativeRelativeProjectiveAmbientIso (T : Over S) (n : ℕ) :
    (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver T.left n).left ≅ HilbertScheme.Presentations.Hilbert.Functor.ambient (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T :=
  (HilbertScheme.Presentations.Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap_isPullback T.hom n).isoIsPullback
    (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n).left T.left
    (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd T (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n))).flip

theorem nativeRelativeProjectiveAmbientIso_projection (T : Over S) (n : ℕ) :
    (nativeRelativeProjectiveAmbientIso T n).hom ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientProjection (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T =
      (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver T.left n).hom :=
  (HilbertScheme.Presentations.Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap_isPullback T.hom n).isoIsPullback_hom_snd _ _ _

theorem nativeRelativeProjectiveAmbientIso_projective (T : Over S) (n : ℕ) :
    (nativeRelativeProjectiveAmbientIso T n).hom ≫
      (prod.snd : T ⨯ HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n ⟶ HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n).left =
        HilbertScheme.Presentations.Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap T.hom n :=
  (HilbertScheme.Presentations.Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap_isPullback T.hom n).isoIsPullback_hom_fst _ _ _

def nativeHilbertAmbientIso (T : Over S) (n : ℕ) :
    (Projective.ProjectivePresentations.projectiveSpaceOver T.left n).left ≅ HilbertScheme.Presentations.Hilbert.Functor.ambient (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T :=
  (Over.forget T.left).mapIso (nativeProjectiveSpaceIso T.left n) ≪≫ nativeRelativeProjectiveAmbientIso T n

theorem nativeHilbertAmbientIso_projection (T : Over S) (n : ℕ) :
    (nativeHilbertAmbientIso T n).hom ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientProjection (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T =
      (Projective.ProjectivePresentations.projectiveSpaceOver T.left n).hom := by
  change ((nativeProjectiveSpaceIso T.left n).hom.left ≫ (nativeRelativeProjectiveAmbientIso T n).hom) ≫ _ = _
  rw [Category.assoc, nativeRelativeProjectiveAmbientIso_projection, nativeProjectiveSpaceIso_projection]

theorem nativeHilbertAmbientIso_projective (T : Over S) (n : ℕ) :
    (nativeHilbertAmbientIso T n).hom ≫
      (prod.snd : T ⨯ HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n ⟶ HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n).left =
      (nativeProjectiveSpaceIso T.left n).hom.left ≫
        HilbertScheme.Presentations.Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap T.hom n := by
  change ((nativeProjectiveSpaceIso T.left n).hom.left ≫ (nativeRelativeProjectiveAmbientIso T n).hom) ≫ _ = _
  rw [Category.assoc, nativeRelativeProjectiveAmbientIso_projective]

theorem nativeHilbertAmbientIso_isPullback (T : Over S) (n : ℕ) :
    IsPullback (nativeHilbertAmbientIso T n).hom (Projective.ProjectivePresentations.projectiveSpaceOver T.left n).hom
      (HilbertScheme.Presentations.Hilbert.Functor.ambientProjection (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T) (𝟙 T.left) :=
  IsPullback.of_horiz_isIso ⟨(nativeHilbertAmbientIso_projection T n).trans (Category.comp_id _).symm⟩

theorem nativeHilbertAmbientIso_affine (T : Over S) (n : ℕ) {R : Type u} [CommRing R]
    (a : Spec (.of R) ⟶ T.left) :
    AffineProjective.Charts.affineProjectiveChartMap a n ≫ (nativeHilbertAmbientIso T n).hom =
      (HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n (a ≫ T.hom)).hom ≫
        HilbertScheme.Presentations.Hilbert.Functor.ambientMap (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n)
          (Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T) := by
  apply (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd T (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n))).hom_ext
  · change (AffineProjective.Charts.affineProjectiveChartMap a n ≫ (nativeHilbertAmbientIso T n).hom) ≫
        HilbertScheme.Presentations.Hilbert.Functor.ambientProjection (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T =
      ((HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n (a ≫ T.hom)).hom ≫
        HilbertScheme.Presentations.Hilbert.Functor.ambientMap (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n)
          (Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T)) ≫
        HilbertScheme.Presentations.Hilbert.Functor.ambientProjection (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T
    rw [Category.assoc, nativeHilbertAmbientIso_projection, AffineProjective.Charts.affineProjectiveChartMap_over,
      affineProjectiveSpace_hom_eq_native, Category.assoc, HilbertScheme.Presentations.Hilbert.AmbientProjections.ambientMap_projection,
      ← Category.assoc, HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso_projection]
    rfl
  · let k : Over.mk (a ≫ T.hom) ⟶ T := Over.homMk a rfl
    let sT : HilbertScheme.Presentations.Hilbert.Functor.ambient (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T ⟶ (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n).left :=
      (prod.snd : T ⨯ HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n ⟶ HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n).left
    let mT := HilbertScheme.Presentations.Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap T.hom n
    have hL : (AffineProjective.Charts.affineProjectiveChartMap a n ≫ (nativeHilbertAmbientIso T n).hom) ≫ sT =
        HilbertScheme.Presentations.Projective.Point.GradedHilbert.projectiveSchemePointMap n (a ≫ T.hom) := by
      have hc : (AffineProjective.Charts.affineProjectiveChartMap a n ≫ (nativeProjectiveSpaceIso T.left n).hom.left) ≫ mT =
          HilbertScheme.Presentations.Projective.Point.GradedHilbert.projectiveSchemePointMap n a ≫ mT :=
        congrArg (fun z : (Projective.ProjectivePresentations.affineProjectiveSpace R n).left ⟶ (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver T.left n).left =>
          z ≫ mT) (nativeProjectiveSpaceIso_affine T.left n a)
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun z => AffineProjective.Charts.affineProjectiveChartMap a n ≫ z) (nativeHilbertAmbientIso_projective T n)).trans
          ((Category.assoc _ _ _).symm.trans (hc.trans (HilbertScheme.Presentations.Projective.PointComposition.GradedHilbert.projectiveSchemePointMap_comp n a T.hom))))
    have hR : ((HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n (a ≫ T.hom)).hom ≫
        HilbertScheme.Presentations.Hilbert.Functor.ambientMap (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) k) ≫ sT = HilbertScheme.Presentations.Projective.Point.GradedHilbert.projectiveSchemePointMap n (a ≫ T.hom) :=
      (Category.assoc _ _ sT).trans
        ((congrArg (fun z => (HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n (a ≫ T.hom)).hom ≫ z)
            (HilbertScheme.Presentations.Hilbert.AmbientProjections.ambientMap_second (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) k)).trans
          (HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso_projective n (a ≫ T.hom)))
    exact hL.trans hR.symm

theorem nativeHilbertAmbientIso_natural {U T : Over S} (a : U ⟶ T) (n : ℕ) :
    RelativeProjective.BaseMaps.relativeProjectiveBaseMap a.left n ≫ (nativeHilbertAmbientIso T n).hom =
      (nativeHilbertAmbientIso U n).hom ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) a := by
  apply (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd T (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n))).hom_ext
  · change (RelativeProjective.BaseMaps.relativeProjectiveBaseMap a.left n ≫ (nativeHilbertAmbientIso T n).hom) ≫
        HilbertScheme.Presentations.Hilbert.Functor.ambientProjection (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T =
      ((nativeHilbertAmbientIso U n).hom ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) a) ≫
        HilbertScheme.Presentations.Hilbert.Functor.ambientProjection (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T
    rw [Category.assoc, nativeHilbertAmbientIso_projection, RelativeProjective.BaseMaps.relativeProjectiveBaseMap_over,
      Category.assoc, HilbertScheme.Presentations.Hilbert.AmbientProjections.ambientMap_projection, ← Category.assoc, nativeHilbertAmbientIso_projection]
  · let sT : HilbertScheme.Presentations.Hilbert.Functor.ambient (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T ⟶ (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n).left :=
      (prod.snd : T ⨯ HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n ⟶ HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n).left
    let mT := HilbertScheme.Presentations.Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap T.hom n
    let mU := HilbertScheme.Presentations.Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap U.hom n
    let mA := HilbertScheme.Presentations.Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap a.left n
    have hL : (RelativeProjective.BaseMaps.relativeProjectiveBaseMap a.left n ≫ (nativeHilbertAmbientIso T n).hom) ≫ sT =
        (nativeProjectiveSpaceIso U.left n).hom.left ≫ mU := by
      calc
        _ = RelativeProjective.BaseMaps.relativeProjectiveBaseMap a.left n ≫ ((nativeHilbertAmbientIso T n).hom ≫ sT) := Category.assoc _ _ _
        _ = RelativeProjective.BaseMaps.relativeProjectiveBaseMap a.left n ≫ ((nativeProjectiveSpaceIso T.left n).hom.left ≫ mT) :=
          congrArg (fun z => RelativeProjective.BaseMaps.relativeProjectiveBaseMap a.left n ≫ z) (nativeHilbertAmbientIso_projective T n)
        _ = (RelativeProjective.BaseMaps.relativeProjectiveBaseMap a.left n ≫ (nativeProjectiveSpaceIso T.left n).hom.left) ≫ mT :=
          (Category.assoc _ _ _).symm
        _ = ((nativeProjectiveSpaceIso U.left n).hom.left ≫ mA) ≫ mT :=
          congrArg (fun z => z ≫ mT) (nativeProjectiveSpaceIso_natural a.left n)
        _ = (nativeProjectiveSpaceIso U.left n).hom.left ≫ (mA ≫ mT) := Category.assoc _ _ _
        _ = (nativeProjectiveSpaceIso U.left n).hom.left ≫
            HilbertScheme.Presentations.Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap (a.left ≫ T.hom) n :=
          congrArg (fun z => (nativeProjectiveSpaceIso U.left n).hom.left ≫ z)
            (HilbertScheme.Presentations.Polynomial.ProjectiveFunctoriality.GradedHilbert.relativeProjectiveBaseMap_comp a.left T.hom n).symm
        _ = (nativeProjectiveSpaceIso U.left n).hom.left ≫ mU :=
          congrArg (fun z : U.left ⟶ S => (nativeProjectiveSpaceIso U.left n).hom.left ≫
            HilbertScheme.Presentations.Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap z n) a.w
    have hR : ((nativeHilbertAmbientIso U n).hom ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) a) ≫ sT =
        (nativeProjectiveSpaceIso U.left n).hom.left ≫ mU :=
      (Category.assoc _ _ sT).trans
        ((congrArg (fun z => (nativeHilbertAmbientIso U n).hom ≫ z)
            (HilbertScheme.Presentations.Hilbert.AmbientProjections.ambientMap_second (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) a)).trans
          (nativeHilbertAmbientIso_projective U n))
    exact hL.trans hR.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.ProjectiveAmbient
