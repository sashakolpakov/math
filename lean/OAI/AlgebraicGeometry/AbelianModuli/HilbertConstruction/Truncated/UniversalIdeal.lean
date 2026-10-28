import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.IdealGluing
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.AffineUniversalData

/-! # Universal Ideal -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.UniversalIdeal

noncomputable section

/-!
The finite graded parameter scheme carries an actual global generated projective
family. Its ideal recovers the generated homogeneous quotient at every affine point.
Higher-degree flatness is not asserted here.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (S : Scheme.{u}) (n B : ℕ) (r : ℕ → ℕ)

def truncatedUniversalIdealData :
    AffineProjective.IdealMatching.AffineProjectiveIdealData (GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S).left n where
  ideal := AffineUniversalData.truncatedAffineUniversalIdeal
  naturality := AffineUniversalData.truncatedAffineUniversalIdeal_naturality

def truncatedUniversalIdeal :
    (Projective.ProjectivePresentations.projectiveSpaceOver (GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S).left n).left.IdealSheafData :=
  (truncatedUniversalIdealData S n B r).glue

theorem truncatedUniversalIdeal_comap {R : CommRingCat.{u}}
    (x : Spec R ⟶ (GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S).left) :
    (truncatedUniversalIdeal S n B r).comap (AffineProjective.Charts.affineProjectiveChartMap x n) =
      (AffineUniversalData.truncatedAffineUniversalData x).projectiveIdeal :=
  (truncatedUniversalIdealData S n B r).glue_comap x

def truncatedUniversalFamily : Over (GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S).left :=
  Over.mk ((truncatedUniversalIdeal S n B r).subschemeι ≫
    (Projective.ProjectivePresentations.projectiveSpaceOver (GradedParameters.truncatedGradedParameters (Fin (n + 1)) B r S).left n).hom)

def truncatedUniversalEmbedding : truncatedUniversalFamily S n B r ⟶
    Projective.ProjectivePresentations.projectiveSpaceOver (GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S).left n :=
  Over.homMk (truncatedUniversalIdeal S n B r).subschemeι rfl

instance truncatedUniversalEmbedding_closed : IsClosedImmersion (truncatedUniversalEmbedding S n B r).left :=
  inferInstanceAs (IsClosedImmersion (truncatedUniversalIdeal S n B r).subschemeι)

def truncatedUniversalProjectivePresentation : Projective.ProjectivePresentations.ProjectivePresentation (truncatedUniversalFamily S n B r) where
  dimension := n
  embedding := truncatedUniversalEmbedding S n B r
  closedImmersion := inferInstance

theorem truncatedUniversalFamily_proper : IsProper (truncatedUniversalFamily S n B r).hom :=
  (truncatedUniversalProjectivePresentation S n B r).proper

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.UniversalIdeal
