import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.LevelRecoveryTarget
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelPointFamilyIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.PresentationIdentity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.LevelProjectionIdentities

/-! # Point Recovery Target -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PointRecoveryTarget.StableHilbertLevel

noncomputable section

/-! Identify the iterated full-level pullback with the actual stable
chart family, retaining the original projective embedding in the equality. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))

def pointIteratedTarget {T : Over (Spec (.of R))}
    (u : T ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels) :
    Embedded.LevelRecoveryTarget.EmbeddedFullLevelTarget T.left g N (Projective.ProjectivePresentations.projectiveSpaceOver T.left n) :=
  Embedded.LevelRecoveryTarget.iteratedEmbeddedFullLevelTarget
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalFamily (Spec (.of R)) n H g Hm Hi N)
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (.of R)) n H g Hm Hi N)
    (HilbertLevel.PullbackParameter.HilbertLevelPullback.toFullLevel (Spec (.of R)) n H g Hm Hi N
      (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
      (ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH)).left
    (LevelParameter.StableHilbertLevel.inclusion R i j D H hH g Hm Hi N labels).left u.left

def pointOriginalTarget {T : Over (Spec (.of R))}
    (u : T ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels) :
    Embedded.LevelRecoveryTarget.EmbeddedFullLevelTarget T.left g N (Projective.ProjectivePresentations.projectiveSpaceOver T.left n) where
  family := (LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels).pullback u.left
  embedding := Embedded.LevelIso.abelianProjectiveBaseChangeEmbedding
    (LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels).abelian
    (LevelParameter.StableHilbertLevel.presentation R i j D H hH g Hm Hi N labels) u.left

private theorem pointRecoveryTarget_family {T : Over (Spec (.of R))}
    (u : T ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels) :
    (pointIteratedTarget R i j D H hH g Hm Hi N labels u).family =
      (pointOriginalTarget R i j D H hH g Hm Hi N labels u).family := rfl

private theorem pointBasePresentation_eq :
    LevelParameter.StableHilbertLevel.basePresentation R i j D H hH g Hm Hi N =
      (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (.of R)) n H g Hm Hi N).baseChange
        (HilbertLevel.PullbackParameter.HilbertLevelPullback.toFullLevel (Spec (.of R)) n H g Hm Hi N
          (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
          (ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH)).left :=
  HilbertLevel.PresentationIdentity.HilbertFullLevelPullback.projective_eq_native (Spec (.of R)) n H g Hm Hi N
    (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
    (ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH)

private abbrev pointIteratedTarget_embedding {T : Over (Spec (.of R))}
    (u : T ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels) :=
  Embedded.LevelProjectionIdentities.iteratedEmbeddedFullLevelTarget_embedding_left
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalFamily (Spec (.of R)) n H g Hm Hi N)
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (.of R)) n H g Hm Hi N)
    (HilbertLevel.PullbackParameter.HilbertLevelPullback.toFullLevel (Spec (.of R)) n H g Hm Hi N
      (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
      (ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH)).left
    (LevelParameter.StableHilbertLevel.inclusion R i j D H hH g Hm Hi N labels).left u.left

private abbrev pointOriginalTarget_embedding {T : Over (Spec (.of R))}
    (u : T ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels) :=
  Embedded.LevelProjectionIdentities.abelianProjectiveBaseChangeEmbedding_left
    (LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels).abelian
    (LevelParameter.StableHilbertLevel.presentation R i j D H hH g Hm Hi N labels) u.left

private abbrev pointRecoveryTarget_embedding {T : Over (Spec (.of R))}
    (u : T ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels) := by
  have h := HilbertLevel.PresentationIdentity.projectiveBaseChangeTwiceEmbedding_heq
    (pointBasePresentation_eq R i j D H hH g Hm Hi N)
    (LevelParameter.StableHilbertLevel.inclusion R i j D H hH g Hm Hi N labels).left u.left
  exact (pointIteratedTarget_embedding R i j D H hH g Hm Hi N labels u).trans
    (h.symm.trans (pointOriginalTarget_embedding R i j D H hH g Hm Hi N labels u).symm)

theorem pointRecoveryTarget_eq {T : Over (Spec (.of R))}
    (u : T ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels) :
    pointIteratedTarget R i j D H hH g Hm Hi N labels u =
      pointOriginalTarget R i j D H hH g Hm Hi N labels u :=
  Embedded.LevelRecoveryTarget.EmbeddedFullLevelTarget.eq_of_family_embedding_left
    (pointRecoveryTarget_family R i j D H hH g Hm Hi N labels u)
    (pointRecoveryTarget_embedding R i j D H hH g Hm Hi N labels u)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PointRecoveryTarget.StableHilbertLevel
