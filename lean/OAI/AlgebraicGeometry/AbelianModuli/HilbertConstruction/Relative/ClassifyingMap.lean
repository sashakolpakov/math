import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.AffineClassifier
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.AffineGluingRecognition

/-! # Classifying Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Actual classifying maps for relative projective Hilbert families on locally noetherian test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {T : Over S} {n B N : ℕ} {P : Polynomial ℚ}
variable (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily T.left n P)
variable (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
variable (hflat : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B) (htest : Truncated.PolynomialTest.truncatedHilbertTestBound n N ≤ B)
variable (hr : Generated.RankTests.GeneratedHilbertRankTest n P N)

def RelativeProjective.Families.RelativeProjectiveHilbertFamily.affineMapData : Noetherian.AffineGluing.NoetherianAffineMapData T.left
    (Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N).left where
  map := F.affineClassifyingMap hN hflat htest hr
  naturality := F.affineClassifyingMap_natural hN hflat htest hr

variable [IsLocallyNoetherian T.left]

def RelativeProjective.Families.RelativeProjectiveHilbertFamily.classifyingMap : T ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N :=
  Over.homMk (F.affineMapData hN hflat htest hr).glue (by
    apply T.left.affineOpenCover.openCover.hom_ext
    intro i
    let := Noetherian.AffineGluing.affineCoverCoordinateRing_noetherian T.left i
    have he : T.left.affineOpenCover.f i ≫ (F.affineMapData hN hflat htest hr).glue =
        F.affineClassifyingMap hN hflat htest hr (T.left.affineOpenCover.f i) :=
      (F.affineMapData hN hflat htest hr).glue_chart i
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a => a ≫ (Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N).hom) he).trans
        (F.affineClassifyingMap_over hN hflat htest hr (T.left.affineOpenCover.f i))))

theorem RelativeProjective.Families.RelativeProjectiveHilbertFamily.classifyingMap_affine {R : CommRingCat.{u}} [IsNoetherianRing R] (x : Spec R ⟶ T.left) :
    x ≫ (F.classifyingMap hN hflat htest hr).left = F.affineClassifyingMap hN hflat htest hr x :=
  (F.affineMapData hN hflat htest hr).glue_affine x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
