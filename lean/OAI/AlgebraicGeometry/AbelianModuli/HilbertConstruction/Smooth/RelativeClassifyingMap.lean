import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.RelativeAffineNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TestGluingRecognition

/-! # Relative Classifying Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Smooth relative Hilbert families have actual global classifying maps over arbitrary test schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {T : Over S} {n B N : ℕ} {P : Polynomial ℚ}
variable (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily T.left n P) [Smooth F.family.scheme.hom]
variable (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N) (hflat : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B)

def RelativeProjective.Families.RelativeProjectiveHilbertFamily.smoothAffineMapData : Affine.TestGluing.AffineTestMapData T.left
    (Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N).left where
  map x := (F.smoothAffinePoint hN hflat x).left
  naturality := F.smoothAffinePoint_natural hN hflat

def RelativeProjective.Families.RelativeProjectiveHilbertFamily.smoothClassifyingMap : T ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N :=
  Over.homMk (F.smoothAffineMapData hN hflat).glue (by
    apply T.left.affineOpenCover.openCover.hom_ext
    intro i
    have he : T.left.affineOpenCover.f i ≫ (F.smoothAffineMapData hN hflat).glue =
        (F.smoothAffinePoint hN hflat (T.left.affineOpenCover.f i)).left :=
      (F.smoothAffineMapData hN hflat).glue_chart i
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a => a ≫ (Truncated.GeneratedParameters.truncatedGeneratedParameters S n B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N) N).hom) he).trans
        (F.smoothAffinePoint hN hflat (T.left.affineOpenCover.f i)).w))

theorem RelativeProjective.Families.RelativeProjectiveHilbertFamily.smoothClassifyingMap_affine {R : CommRingCat.{u}} (x : Spec R ⟶ T.left) :
    x ≫ (F.smoothClassifyingMap hN hflat).left = (F.smoothAffinePoint hN hflat x).left :=
  (F.smoothAffineMapData hN hflat).glue_affine x

theorem RelativeProjective.Families.RelativeProjectiveHilbertFamily.smoothClassifyingMap_pullback {R : CommRingCat.{u}} (x : Spec R ⟶ T.left) :
    Generated.PullbackAffineCharts.generatedPullbackFamilyAtAffinePoint (x ≫ (F.smoothClassifyingMap hN hflat).left) hflat =
      (F.affineFamily x).val := by
  rw [F.smoothClassifyingMap_affine hN hflat]
  exact F.smoothAffinePoint_pullback hN hflat x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
