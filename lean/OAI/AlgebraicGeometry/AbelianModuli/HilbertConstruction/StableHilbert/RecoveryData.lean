import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.LevelEmbeddedRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PrescribedPointLift
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PointRecoveryTarget

/-! # Recovery Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.RecoveryData.StableHilbertAbelianPointRecovery

noncomputable section

/-! Recover an original family from its native full-level Hilbert data
and its prescribed ordered marks on the stable chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))

private theorem data_markedPoint {T : Over (Spec (.of R))}
    (c : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
    (A : Abelian.Schemes.AbelianScheme g T.left) (level : A.FullLevel N)
    (k : A.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver T.left n)
    (data : Intrinsic.LevelRecoveryData.NativeFullLevelRecoveryData (Spec (.of R)) n H g Hm Hi N T A level
      (c ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH) k.left)
    (hpoints : ∀ z, A.fullLevelGlobalSection level (labels z) ≫ k.left =
      (PrescribedPointCriterion.stableHilbertPrescribedPoint R i j D H c z).left) (z : Fin m) :
    HilbertLevel.MarkedUniqueness.HilbertLevelPullback.markedPoint (Spec (.of R)) n H g Hm Hi N data.point (labels z) =
      PrescribedPointCriterion.stableHilbertPrescribedPoint R i j D H c z := by
  apply Over.OverMorphism.ext
  exact (data.marked_eq (labels z)).trans (hpoints z)

private theorem data_pointRecovery {T : Over (Spec (.of R))}
    (c : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
    (A : Abelian.Schemes.AbelianScheme g T.left) (level : A.FullLevel N)
    (k : A.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver T.left n)
    (data : Intrinsic.LevelRecoveryData.NativeFullLevelRecoveryData (Spec (.of R)) n H g Hm Hi N T A level
      (c ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH) k.left)
    (u : T ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels)
    (hrec : PrescribedPointLift.StableHilbertLevel.pointFamilyRecoveryProperty
      R i j D H hH g Hm Hi N labels data.point u) :
    Embedded.LevelIso.EmbeddedFullLevelRecovery A level
      ((LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels).pullback u.left)
      k (Embedded.LevelIso.abelianProjectiveBaseChangeEmbedding
        (LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels).abelian
        (LevelParameter.StableHilbertLevel.presentation R i j D H hH g Hm Hi N labels) u.left) := by
  exact Embedded.LevelRecoveryTarget.EmbeddedFullLevelTarget.changeTarget
    (PointRecoveryTarget.StableHilbertLevel.pointRecoveryTarget_eq R i j D H hH g Hm Hi N labels u)
    (data.iteratedRecovery hrec)

theorem exists_recovery_of_data {T : Over (Spec (.of R))}
    (c : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
    (A : Abelian.Schemes.AbelianScheme g T.left) (level : A.FullLevel N)
    (k : A.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver T.left n)
    (data : Intrinsic.LevelRecoveryData.NativeFullLevelRecoveryData (Spec (.of R)) n H g Hm Hi N T A level
      (c ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH) k.left)
    (hpoints : ∀ z, A.fullLevelGlobalSection level (labels z) ≫ k.left =
      (PrescribedPointCriterion.stableHilbertPrescribedPoint R i j D H c z).left) :
    ∃ u : T ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels,
      u ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels = c ∧
      Embedded.LevelIso.EmbeddedFullLevelRecovery A level
        ((LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels).pullback u.left)
        k (Embedded.LevelIso.abelianProjectiveBaseChangeEmbedding
          (LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels).abelian
          (LevelParameter.StableHilbertLevel.presentation R i j D H hH g Hm Hi N labels) u.left) := by
  obtain ⟨u, hu, hrec⟩ := PrescribedPointLift.StableHilbertLevel.exists_familyRecovery
    R i j D H hH g Hm Hi N labels c data.point data.forget_eq
    (data_markedPoint R i j D H hH g Hm Hi N labels c A level k data hpoints)
  exact ⟨u, hu, data_pointRecovery R i j D H hH g Hm Hi N labels c A level k data u hrec⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.RecoveryData.StableHilbertAbelianPointRecovery
