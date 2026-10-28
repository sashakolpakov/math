import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.UniversalIdeal
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed.IdealChartPullback

/-! # Universal Family Charts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.UniversalFamilyCharts

noncomputable section

/-! Every affine pullback of the global generated family is the actual generated homogeneous projective quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {n B : ℕ} {r : ℕ → ℕ} {R : CommRingCat.{u}}
variable (x : Spec R ⟶ (GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S).left)

def truncatedUniversalFamilyChartMap :
    (AffineUniversalData.truncatedAffineUniversalData x).projectiveFamily.left ⟶ (UniversalIdeal.truncatedUniversalFamily S n B r).left :=
  Closed.IdealChartPullback.closedIdealChartMap (UniversalIdeal.truncatedUniversalIdeal S n B r)
    (AffineUniversalData.truncatedAffineUniversalData x).projectiveEmbedding.left (AffineProjective.Charts.affineProjectiveChartMap x n)
      (UniversalIdeal.truncatedUniversalIdeal_comap S n B r x)

theorem truncatedUniversalFamilyChartMap_embedding :
    truncatedUniversalFamilyChartMap x ≫ (UniversalIdeal.truncatedUniversalEmbedding S n B r).left =
      (AffineUniversalData.truncatedAffineUniversalData x).projectiveEmbedding.left ≫ AffineProjective.Charts.affineProjectiveChartMap x n :=
  Closed.IdealChartPullback.closedIdealChartMap_embedding _ _ _ _

theorem truncatedUniversalFamilyChart_isPullback :
    IsPullback (truncatedUniversalFamilyChartMap x) (AffineUniversalData.truncatedAffineUniversalData x).projectiveFamily.hom
      (UniversalIdeal.truncatedUniversalFamily S n B r).hom x := by
  have h := Closed.IdealChartPullback.closedIdealChartFamily_isPullback (UniversalIdeal.truncatedUniversalIdeal S n B r)
    (AffineUniversalData.truncatedAffineUniversalData x).projectiveEmbedding.left (AffineProjective.Charts.affineProjectiveChartMap x n)
      (UniversalIdeal.truncatedUniversalIdeal_comap S n B r x) (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom
        (Projective.ProjectivePresentations.projectiveSpaceOver (GradedParameters.truncatedGradedParameters (Fin (n + 1)) B r S).left n).hom x
          (AffineProjective.Charts.affineProjectiveChartMap_isPullback x n)
  have he := (AffineUniversalData.truncatedAffineUniversalData x).projectiveEmbedding.w
  rw [he] at h
  exact h

def truncatedUniversalFamilyAffineIso :
    (AffineUniversalData.truncatedAffineUniversalData x).projectiveFamily ≅
      (Over.pullback x).obj (UniversalIdeal.truncatedUniversalFamily S n B r) :=
  Over.isoMk (truncatedUniversalFamilyChart_isPullback x).isoPullback
    (truncatedUniversalFamilyChart_isPullback x).isoPullback_hom_snd

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.UniversalFamilyCharts
