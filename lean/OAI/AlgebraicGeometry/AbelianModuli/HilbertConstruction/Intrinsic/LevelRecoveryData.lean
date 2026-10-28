import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.LevelRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.LevelIso

/-! # Level Recovery Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.LevelRecoveryData

noncomputable section

/-! The original native classifier and all its recovery laws are kept
together before specialization to a stable Hilbert chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

structure NativeFullLevelRecoveryData
    (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (H : Polynomial ℚ)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (T : Over S) (A : Abelian.Schemes.AbelianScheme g T.left) (level : A.FullLevel N)
    (b : T ⟶ Hilbert.ParameterScheme.hilbertParameterScheme S n H)
    (k : A.scheme.left ⟶ (Projective.ProjectivePresentations.projectiveSpaceOver T.left n).left) where
  point : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n H g Hm Hi N
  iso : A.scheme ≅
    ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S n H g Hm Hi N).pullback point.left).scheme
  group : IsMonHom iso.hom
  level_eq :
    let _ : IsMonHom iso.hom := group
    level.transport iso = (FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel S n H g Hm Hi N).pullback point.left
  forget_eq : point ≫ HilbertLevel.PullbackParameter.HilbertLevelPullback.forget S n H g Hm Hi N = b
  embedding_eq : iso.hom.left ≫
    ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n H g Hm Hi N).baseChange
      point.left).embedding.left = k
  marked_eq : ∀ label : Multiplicative (Fin (2 * g) → ZMod N),
    (HilbertLevel.MarkedUniqueness.HilbertLevelPullback.markedPoint S n H g Hm Hi N point label).left =
      A.fullLevelGlobalSection level label ≫ k

def nativeFullLevelRecoveryData
    (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (H : Polynomial ℚ) (g : ℕ)
    {T : Over S} (A : Abelian.Schemes.AbelianScheme g T.left)
    (b : T ⟶ Hilbert.ParameterScheme.hilbertParameterScheme S n H)
    (e : A.scheme ≅ (Over.pullback b.left).obj (Hilbert.ParameterScheme.hilbertUniversalFamily S n H).family.scheme)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (eL : (((Presentation.NativeHilbertAbelianLift.presentation S n H).baseChange b.left).ampleLineBundle.pullback
      e.hom.left).sheaf ≅ P.ampleLineBundle.sheaf)
    (Hm Hi : Polynomial ℚ)
    (hb : (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj A.scheme).ProjectiveGraphBounds P Hm Hi)
    (N : ℕ) [NeZero N] (level : A.FullLevel N)
    (k : A.scheme.left ⟶ (Projective.ProjectivePresentations.projectiveSpaceOver T.left n).left)
    (he : e.hom.left ≫ ((Presentation.NativeHilbertAbelianLift.presentation S n H).baseChange b.left).embedding.left = k) :
    NativeFullLevelRecoveryData S n H g Hm Hi N T A level b k where
  point := AbelianLift.NativeHilbertAbelianLift.fullLevelClassifier S n H g A b e P eL Hm Hi hb N level
  iso := LevelRecovery.IntrinsicHilbertAbelianLift.fullLevelRecovery S n H g A b e P eL Hm Hi hb N level
  group := LevelRecovery.IntrinsicHilbertAbelianLift.fullLevelRecovery_isMonHom S n H g A b e P eL Hm Hi hb N level
  level_eq := LevelRecovery.IntrinsicHilbertAbelianLift.fullLevelRecovery_level S n H g A b e P eL Hm Hi hb N level
  forget_eq := AbelianLift.NativeHilbertAbelianLift.fullLevelClassifier_forget S n H g A b e P eL Hm Hi hb N level
  embedding_eq := (LevelRecovery.IntrinsicHilbertAbelianLift.fullLevelRecovery_embedding_left
    S n H g A b e P eL Hm Hi hb N level).trans he
  marked_eq label := (LevelRecovery.IntrinsicHilbertAbelianLift.fullLevelClassifier_markedSection
    S n H g A b e P eL Hm Hi hb N level label).trans
      (congrArg (fun f => A.fullLevelGlobalSection level label ≫ f) he)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.LevelRecoveryData
