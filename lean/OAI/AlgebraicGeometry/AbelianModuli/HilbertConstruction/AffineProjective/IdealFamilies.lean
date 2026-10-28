import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.IdealPrecomposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.IdealChartPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.Families

/-! # Ideal Families -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective

noncomputable section

/-! Compatible affine projective ideals define an actual global closed family, whose affine pullbacks recover the given ideals and whose geometric properties descend from affine bases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {n : ℕ} (D : IdealMatching.AffineProjectiveIdealData S n)

def IdealMatching.AffineProjectiveIdealData.family : Over S := Over.mk (D.glue.subschemeι ≫ (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom)

def IdealMatching.AffineProjectiveIdealData.affineFamily {R : CommRingCat.{u}} (x : Spec R ⟶ S) : Over (Spec R) :=
  Over.mk ((D.ideal x).subschemeι ≫ (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom)

def IdealMatching.AffineProjectiveIdealData.familyChartMap {R : CommRingCat.{u}} (x : Spec R ⟶ S) :
    (D.affineFamily x).left ⟶ D.family.left :=
  Closed.IdealChartPullback.closedIdealChartMap D.glue (D.ideal x).subschemeι (Charts.affineProjectiveChartMap x n)
    ((D.glue_comap x).trans (D.ideal x).ker_subschemeι.symm)

theorem IdealMatching.AffineProjectiveIdealData.familyChart_isPullback {R : CommRingCat.{u}} (x : Spec R ⟶ S) :
    IsPullback (D.familyChartMap x) (D.affineFamily x).hom D.family.hom x :=
  Closed.IdealChartPullback.closedIdealChartFamily_isPullback D.glue (D.ideal x).subschemeι (Charts.affineProjectiveChartMap x n)
    ((D.glue_comap x).trans (D.ideal x).ker_subschemeι.symm)
      (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom x (Charts.affineProjectiveChartMap_isPullback x n)

def IdealMatching.AffineProjectiveIdealData.familyAffineIso {R : CommRingCat.{u}} (x : Spec R ⟶ S) :
    D.affineFamily x ≅ (Over.pullback x).obj D.family :=
  Over.isoMk (D.familyChart_isPullback x).isoPullback (D.familyChart_isPullback x).isoPullback_hom_snd

theorem IdealMatching.AffineProjectiveIdealData.family_property (W : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget W]
    (hW : ∀ i : S.affineOpenCover.I₀, W (D.affineFamily (S.affineOpenCover.f i)).hom) : W D.family.hom := by
  apply IsZariskiLocalAtTarget.of_openCover (P := W) S.affineOpenCover.openCover
  intro i
  let h := D.familyChart_isPullback (S.affineOpenCover.f i)
  have hh : W (h.isoPullback.inv ≫ (D.affineFamily (S.affineOpenCover.f i)).hom) :=
    (W.cancel_left_of_respectsIso _ _).mpr (hW i)
  have he : h.isoPullback.inv ≫ (D.affineFamily (S.affineOpenCover.f i)).hom =
      S.affineOpenCover.openCover.pullbackHom D.family.hom i := h.isoPullback_inv_snd
  exact he ▸ hh

def IdealMatching.AffineProjectiveIdealData.flatClosedFamily
    (hflat : ∀ i : S.affineOpenCover.I₀, Flat (D.affineFamily (S.affineOpenCover.f i)).hom)
    (hfinite : ∀ i : S.affineOpenCover.I₀,
      LocallyOfFinitePresentation (D.affineFamily (S.affineOpenCover.f i)).hom) :
    Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.projectiveSpaceOver S n) where
  ideal := D.glue
  flat := by
    let : IsZariskiLocalAtTarget (@Flat.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat.{u}) (Q := RingHom.Flat)
    exact D.family_property (@Flat) hflat
  locallyFinitePresentation := by
    let : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtTarget
        (P := @LocallyOfFinitePresentation.{u}) (Q := RingHom.FinitePresentation)
    exact D.family_property (@LocallyOfFinitePresentation) hfinite

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective
