import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelForgetful
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.LevelIso

/-! # Level Point Family Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelPointFamilyIso.StableHilbertLevel

noncomputable section

/-! The two original parameter pullback isomorphisms identify a stable
full-level chart fiber with its original full-level Hilbert fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))

variable {T : Over (Spec (CommRingCat.of R))} (u : T ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels)

def pointFamilyBasePoint : Over.mk (u ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels).left ⟶ Over.mk ((HilbertLevel.PullbackParameter.HilbertLevelPullback.toFullLevel (Spec (CommRingCat.of R)) n H g Hm Hi N
      (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
      (ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH))).left :=
  Over.homMk (u ≫ (LevelParameter.StableHilbertLevel.inclusion R i j D H hH g Hm Hi N labels)).left (congrArg Over.Hom.left (Category.assoc u (LevelParameter.StableHilbertLevel.inclusion R i j D H hH g Hm Hi N labels) (HilbertLevel.PullbackParameter.HilbertLevelPullback.toFullLevel (Spec (CommRingCat.of R)) n H g Hm Hi N
      (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
      (ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH))))

def pointFamilyMarkedPointMap : Over.mk (u ≫ (LevelParameter.StableHilbertLevel.inclusion R i j D H hH g Hm Hi N labels)).left ⟶ Over.mk ((LevelParameter.StableHilbertLevel.inclusion R i j D H hH g Hm Hi N labels)).left := Over.homMk u.left rfl

/-- The original two pullback comparisons with their group, level, and
embedding identities checked at the same parameter points. -/
def pointFamilyRecovery :
  Embedded.LevelIso.ParameterPullbackTwiceRecovery (g := g) (N := N) ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalFamily (Spec (CommRingCat.of R)) n H g Hm Hi N)) ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (CommRingCat.of R)) n H g Hm Hi N))
    (U := Over.mk (u ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels).left)
    (T := Over.mk ((HilbertLevel.PullbackParameter.HilbertLevelPullback.toFullLevel (Spec (CommRingCat.of R)) n H g Hm Hi N
      (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
      (ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH))).left)
    (Over.homMk (u ≫ (LevelParameter.StableHilbertLevel.inclusion R i j D H hH g Hm Hi N labels)).left (congrArg Over.Hom.left (Category.assoc u (LevelParameter.StableHilbertLevel.inclusion R i j D H hH g Hm Hi N labels) (HilbertLevel.PullbackParameter.HilbertLevelPullback.toFullLevel (Spec (CommRingCat.of R)) n H g Hm Hi N
      (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
      (ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH)))))
    (V := Over.mk ((LevelParameter.StableHilbertLevel.inclusion R i j D H hH g Hm Hi N labels)).left) (Over.homMk u.left rfl) :=
  Embedded.LevelIso.parameterPullbackTwiceRecovery _ _ _ _

/-- The same composition of the two native parameter pullback isomorphisms. -/
def pointFamilyIso :
    (((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalFamily (Spec (CommRingCat.of R)) n H g Hm Hi N)).pullback (u ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels).left).abelian.scheme ≅
      ((LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels).pullback u.left).abelian.scheme :=
  (pointFamilyRecovery R i j D H hH g Hm Hi N labels u).data.data.iso

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelPointFamilyIso.StableHilbertLevel
