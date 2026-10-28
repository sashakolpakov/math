import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelFamilyComparison

/-! # Prescribed Point Lift -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PrescribedPointLift.StableHilbertLevel

noncomputable section

/-! An original marked Hilbert point lifts to the stable chart with
both projections retained. Its original group and full level are then
recovered on the actual stable-chart family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))

theorem exists_prescribedPoint {T : Over (Spec (CommRingCat.of R))}
    (c : T ⟶ (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)) (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter (Spec (CommRingCat.of R)) n H g Hm Hi N)
    (hy : y ≫ HilbertLevel.PullbackParameter.HilbertLevelPullback.forget (Spec (CommRingCat.of R)) n H g Hm Hi N = c ≫ (ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH))
    (hm : ∀ z, HilbertLevel.MarkedUniqueness.HilbertLevelPullback.markedPoint (Spec (CommRingCat.of R)) n H g Hm Hi N y (labels z) =
      PrescribedPointCriterion.stableHilbertPrescribedPoint R i j D H c z) :
    ∃ u : T ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels,
      u ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels = c ∧
      u ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels = y := by
  let a : T ⟶ (LevelParameter.StableHilbertLevel.base R i j D H hH g Hm Hi N) := pullback.lift c y hy.symm
  have ha : a ≫ LevelParameter.StableHilbertLevel.toChart R i j D H hH g Hm Hi N = c := pullback.lift_fst _ _ _
  have hh : a ≫ (HilbertLevel.PullbackParameter.HilbertLevelPullback.toFullLevel (Spec (CommRingCat.of R)) n H g Hm Hi N (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H) (ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH)) = y := pullback.lift_snd _ _ _
  have hap : PrescribedLevelAmbientParameter.PrescribedFullLevelAmbientAt (LevelParameter.StableHilbertLevel.base R i j D H hH g Hm Hi N) (LevelParameter.StableHilbertLevel.baseFamily R i j D H hH g Hm Hi N).abelian
      (LevelParameter.StableHilbertLevel.baseFamily R i j D H hH g Hm Hi N).level (LevelParameter.StableHilbertLevel.basePresentation R i j D H hH g Hm Hi N)
      labels (LevelParameter.StableHilbertLevel.markedPoint R i j D H hH g Hm Hi N) a.left := by
    apply (HilbertLevel.PrescribedCriterion.HilbertFullLevelPullback.prescribed_iff_markedPoint (Spec (CommRingCat.of R)) n H g Hm Hi N
      (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H) (ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH) labels (LevelParameter.StableHilbertLevel.markedPoint R i j D H hH g Hm Hi N) a).mpr
    intro z
    have hx := PrescribedPointCriterion.StableHilbertFullLevel.markedPoint_baseChange_chartPoint R i j D H hH g Hm Hi N a z
    exact (congrArg (fun b => HilbertLevel.MarkedUniqueness.HilbertLevelPullback.markedPoint (Spec (CommRingCat.of R)) n H g Hm Hi N
      b (labels z)) hh).trans ((hm z).trans
        ((congrArg (fun b => PrescribedPointCriterion.stableHilbertPrescribedPoint R i j D H b z) ha).symm.trans hx.symm))
  let u := (LevelParameter.StableHilbertLevel.pointEquiv R i j D H hH g Hm Hi N labels T).symm ⟨a, hap⟩
  have hu : u ≫ LevelParameter.StableHilbertLevel.inclusion R i j D H hH g Hm Hi N labels = a :=
    congrArg Subtype.val ((LevelParameter.StableHilbertLevel.pointEquiv R i j D H hH g Hm Hi N labels T).apply_symm_apply ⟨a, hap⟩)
  refine ⟨u, ?_, ?_⟩
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun b => b ≫ LevelParameter.StableHilbertLevel.toChart R i j D H hH g Hm Hi N) hu).trans ha)
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (fun b => b ≫ (HilbertLevel.PullbackParameter.HilbertLevelPullback.toFullLevel (Spec (CommRingCat.of R)) n H g Hm Hi N (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H) (ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH))) hu).trans hh)

def pointFamilyRecoveryProperty {T : Over (Spec (.of R))}
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter (Spec (.of R)) n H g Hm Hi N)
    (u : T ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels) : Prop :=
  Embedded.LevelIso.IteratedFullLevelFamilyRecovery
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalFamily (Spec (.of R)) n H g Hm Hi N)
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation (Spec (.of R)) n H g Hm Hi N)
    (HilbertLevel.PullbackParameter.HilbertLevelPullback.toFullLevel (Spec (.of R)) n H g Hm Hi N
      (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
      (ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH)).left
    (LevelParameter.StableHilbertLevel.inclusion R i j D H hH g Hm Hi N labels).left y.left u.left

theorem exists_familyRecovery {T : Over (Spec (.of R))}
    (c : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter (Spec (.of R)) n H g Hm Hi N)
    (hy : y ≫ HilbertLevel.PullbackParameter.HilbertLevelPullback.forget (Spec (.of R)) n H g Hm Hi N =
      c ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH)
    (hm : ∀ z, HilbertLevel.MarkedUniqueness.HilbertLevelPullback.markedPoint (Spec (.of R)) n H g Hm Hi N y (labels z) =
      PrescribedPointCriterion.stableHilbertPrescribedPoint R i j D H c z) :
    ∃ u : T ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels,
      u ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels = c ∧
      pointFamilyRecoveryProperty R i j D H hH g Hm Hi N labels y u := by
  exact Embedded.LevelIso.pointLift_with_fiberProperty
    (fun u : T ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels =>
      u ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels)
    (fun u : T ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels =>
      u ≫ LevelForgetful.StableHilbertFullLevel.toFullLevel R i j D H hH g Hm Hi N labels)
    c y (pointFamilyRecoveryProperty R i j D H hH g Hm Hi N labels (T := T))
    (exists_prescribedPoint R i j D H hH g Hm Hi N labels c y hy hm)
    (fun u => (LevelPointFamilyIso.StableHilbertLevel.pointFamilyRecovery R i j D H hH g Hm Hi N labels u).originalFamilyRecovery)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PrescribedPointLift.StableHilbertLevel
