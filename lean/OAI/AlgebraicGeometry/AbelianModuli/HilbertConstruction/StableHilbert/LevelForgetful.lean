import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PrescribedPointCriterion

/-! # Level Forgetful -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelForgetful.StableHilbertFullLevel

noncomputable section

/-! Forgetting a stable marked chart to its original full-level Hilbert
point preserves the Hilbert point and every prescribed marked section. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))

def toFullLevel : LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels ⟶
    FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter (Spec (.of R)) n H g Hm Hi N :=
  LevelParameter.StableHilbertLevel.inclusion R i j D H hH g Hm Hi N labels ≫
    HilbertLevel.PullbackParameter.HilbertLevelPullback.toFullLevel (Spec (.of R)) n H g Hm Hi N
      (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H) (ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH)

theorem toFullLevel_forget :
    toFullLevel R i j D H hH g Hm Hi N labels ≫
      HilbertLevel.PullbackParameter.HilbertLevelPullback.forget (Spec (.of R)) n H g Hm Hi N =
    LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH := by
  let inc := LevelParameter.StableHilbertLevel.inclusion R i j D H hH g Hm Hi N labels
  exact (Category.assoc _ _ _).trans ((congrArg (fun a => inc ≫ a)
    (HilbertLevel.PullbackParameter.HilbertLevelPullback.parameter_square (Spec (.of R)) n H g Hm Hi N
      (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H) (ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH)).symm).trans
      (Category.assoc _ _ _).symm)

theorem point_forget {T : Over (Spec (.of R))} (u : T ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels) :
    (u ≫ toFullLevel R i j D H hH g Hm Hi N labels) ≫
      HilbertLevel.PullbackParameter.HilbertLevelPullback.forget (Spec (.of R)) n H g Hm Hi N =
    (u ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels) ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH :=
  (Category.assoc _ _ _).trans ((congrArg (fun a => u ≫ a)
    (toFullLevel_forget R i j D H hH g Hm Hi N labels)).trans (Category.assoc _ _ _).symm)

theorem point_markedPoint {T : Over (Spec (.of R))}
    (u : T ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels) (z : Fin m) :
    HilbertLevel.MarkedUniqueness.HilbertLevelPullback.markedPoint (Spec (.of R)) n H g Hm Hi N
      (u ≫ toFullLevel R i j D H hH g Hm Hi N labels) (labels z) =
    PrescribedPointCriterion.stableHilbertPrescribedPoint R i j D H (u ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels) z := by
  let a := u ≫ LevelParameter.StableHilbertLevel.inclusion R i j D H hH g Hm Hi N labels
  have ha : PrescribedLevelAmbientParameter.PrescribedFullLevelAmbientAt (LevelParameter.StableHilbertLevel.base R i j D H hH g Hm Hi N)
      (LevelParameter.StableHilbertLevel.baseFamily R i j D H hH g Hm Hi N).abelian (LevelParameter.StableHilbertLevel.baseFamily R i j D H hH g Hm Hi N).level
      (LevelParameter.StableHilbertLevel.basePresentation R i j D H hH g Hm Hi N) labels (LevelParameter.StableHilbertLevel.markedPoint R i j D H hH g Hm Hi N) a.left :=
    (LevelParameter.StableHilbertLevel.pointEquiv R i j D H hH g Hm Hi N labels T u).property
  have hm := HilbertLevel.PrescribedUniqueness.HilbertLevelPullback.markedPoint_of_prescribed (Spec (.of R)) n H g Hm Hi N
    (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H) (ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH)
    labels (LevelParameter.StableHilbertLevel.markedPoint R i j D H hH g Hm Hi N) a ha z
  have hc := PrescribedPointCriterion.StableHilbertFullLevel.markedPoint_baseChange_chartPoint R i j D H hH g Hm Hi N a z
  let p := HilbertLevel.PullbackParameter.HilbertLevelPullback.toFullLevel (Spec (.of R)) n H g Hm Hi N
    (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H) (ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH)
  have hleft : u ≫ toFullLevel R i j D H hH g Hm Hi N labels = a ≫ p :=
    (Category.assoc u (LevelParameter.StableHilbertLevel.inclusion R i j D H hH g Hm Hi N labels) p).symm
  have hright : a ≫ LevelParameter.StableHilbertLevel.toChart R i j D H hH g Hm Hi N =
      u ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels :=
    Category.assoc u (LevelParameter.StableHilbertLevel.inclusion R i j D H hH g Hm Hi N labels)
      (LevelParameter.StableHilbertLevel.toChart R i j D H hH g Hm Hi N)
  exact (congrArg (fun y => HilbertLevel.MarkedUniqueness.HilbertLevelPullback.markedPoint
    (Spec (.of R)) n H g Hm Hi N y (labels z)) hleft).trans
      (hm.trans (hc.trans (congrArg (fun c => PrescribedPointCriterion.stableHilbertPrescribedPoint R i j D H c z) hright)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelForgetful.StableHilbertFullLevel
