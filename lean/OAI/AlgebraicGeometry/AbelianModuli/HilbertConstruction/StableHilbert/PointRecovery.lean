import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.RecoveryData

/-! # Point Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PointRecovery.StableHilbertAbelianPointRecovery

noncomputable section

/-! An original abelian family whose native Hilbert fiber has the
prescribed ordered projective marks lifts to the actual stable
full-level chart. The lift recovers its original embedding and level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))

theorem exists_recovery {T : Over (Spec (.of R))}
    (c : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
    (A : Abelian.Schemes.AbelianScheme g T.left) (level : A.FullLevel N)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (e : A.scheme ≅
      (Over.pullback (c ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH).left).obj
        (Hilbert.ParameterScheme.hilbertUniversalFamily (Spec (.of R)) n H).family.scheme)
    (eL : ((((Intrinsic.Presentation.NativeHilbertAbelianLift.presentation (Spec (.of R)) n H)).baseChange (c ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH).left).ampleLineBundle.pullback
      e.hom.left).sheaf ≅ P.ampleLineBundle.sheaf)
    (hb : (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj A.scheme).ProjectiveGraphBounds P Hm Hi)
    (hpoints : ∀ z, A.fullLevelGlobalSection level (labels z) ≫ e.hom.left ≫
      (((Intrinsic.Presentation.NativeHilbertAbelianLift.presentation (Spec (.of R)) n H)).baseChange (c ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH).left).embedding.left =
        (PrescribedPointCriterion.stableHilbertPrescribedPoint R i j D H c z).left) :
    ∃ u : T ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels,
      u ≫ LevelMonomorphism.StableHilbertLevel.toHilbertChart R i j D H hH g Hm Hi N labels = c ∧
      Embedded.LevelIso.EmbeddedFullLevelRecovery A level
        ((LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels).pullback u.left)
        (e.hom ≫ ((Intrinsic.Presentation.NativeHilbertAbelianLift.presentation (Spec (.of R)) n H).baseChange
          (c ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH).left).embedding)
        (Embedded.LevelIso.abelianProjectiveBaseChangeEmbedding
          (LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels).abelian
          (LevelParameter.StableHilbertLevel.presentation R i j D H hH g Hm Hi N labels) u.left) := by
  exact RecoveryData.StableHilbertAbelianPointRecovery.exists_recovery_of_data R i j D H hH g Hm Hi N labels c A level _
    (Intrinsic.LevelRecoveryData.nativeFullLevelRecoveryData (Spec (.of R)) n H g A
      (c ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH) e P eL Hm Hi hb N level _ rfl)
    hpoints

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PointRecovery.StableHilbertAbelianPointRecovery
