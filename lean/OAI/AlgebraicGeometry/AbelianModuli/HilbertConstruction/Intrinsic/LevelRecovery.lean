import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AbelianLift
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.MarkedUniqueness

/-! # Level Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.LevelRecovery.IntrinsicHilbertAbelianLift

noncomputable section

/-! The full-level lift of an original abelian Hilbert fiber recovers
the original group, every level label, and its exact projective embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (H : Polynomial ℚ) (g : ℕ)
    {T : Over S} (A : Abelian.Schemes.AbelianScheme g T.left)
    (b : T ⟶ Hilbert.ParameterScheme.hilbertParameterScheme S n H)
    (e : A.scheme ≅ (Over.pullback b.left).obj (Hilbert.ParameterScheme.hilbertUniversalFamily S n H).family.scheme)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (eL : (((Presentation.NativeHilbertAbelianLift.presentation S n H).baseChange b.left).ampleLineBundle.pullback e.hom.left).sheaf ≅
      P.ampleLineBundle.sheaf)
    (Hm Hi : Polynomial ℚ)
    (hb : (FamilyGroup.Operations.FamilyGroupOperations.ofGrpObj A.scheme).ProjectiveGraphBounds P Hm Hi)
    (N : ℕ) [NeZero N] (level : A.FullLevel N)

local notation "c" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AbelianLift.NativeHilbertAbelianLift.classifier S n H g A b e
local notation "r" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AbelianLift.NativeHilbertAbelianLift.recovery S n H g A b e
local notation "rL" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AbelianLift.NativeHilbertAbelianLift.recoveryTwistingIso S n H g A b e P eL
local notation "y" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AbelianLift.NativeHilbertAbelianLift.fullLevelClassifier S n H g A b e P eL Hm Hi hb N level

def fullLevelRecovery : A.scheme ≅
    ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S n H g Hm Hi N).pullback (y).left).scheme :=
  LevelReembedding.NativeHilbertFullLevelReembedding.recovery S n H g Hm Hi A P c r rL hb N level

instance fullLevelRecovery_isMonHom :
    IsMonHom (fullLevelRecovery S n H g A b e P eL Hm Hi hb N level).hom :=
  inferInstanceAs (IsMonHom
    (LevelReembedding.NativeHilbertFullLevelReembedding.recovery S n H g Hm Hi A P c r rL hb N level).hom)

theorem fullLevelRecovery_level :
    level.transport (fullLevelRecovery S n H g A b e P eL Hm Hi hb N level) =
      (FixedDimension.LevelParameters.fixedDimensionHilbertUniversalFullLevel S n H g Hm Hi N).pullback (y).left :=
  LevelReembedding.NativeHilbertFullLevelReembedding.recovery_level S n H g Hm Hi A P c r rL hb N level

omit [AlgebraicGeometry.IsNoetherian S] in
private theorem originalRecovery_embedding_left :
    (r).hom.left ≫
      ((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n H g).baseChange (c).left).embedding.left =
      e.hom.left ≫ ((Presentation.NativeHilbertAbelianLift.presentation S n H).baseChange b.left).embedding.left :=
  congrArg (fun f : A.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver T.left n => f.left)
    (AbelianLift.NativeHilbertAbelianLift.recovery_embedding S n H g A b e)

private theorem fullLevelRecovery_fixedEmbedding_left :
    (fullLevelRecovery S n H g A b e P eL Hm Hi hb N level).hom.left ≫
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n H g Hm Hi N).baseChange
        (y).left).embedding.left =
      (r).hom.left ≫
        ((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n H g).baseChange (c).left).embedding.left :=
  congrArg (fun f : A.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver T.left n => f.left)
    (LevelReembedding.NativeHilbertFullLevelReembedding.recovery_embedding S n H g Hm Hi A P c r rL hb N level)

theorem fullLevelRecovery_embedding_left :
    (fullLevelRecovery S n H g A b e P eL Hm Hi hb N level).hom.left ≫
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n H g Hm Hi N).baseChange
        (y).left).embedding.left =
      e.hom.left ≫ ((Presentation.NativeHilbertAbelianLift.presentation S n H).baseChange b.left).embedding.left :=
  (fullLevelRecovery_fixedEmbedding_left S n H g A b e P eL Hm Hi hb N level).trans
    (originalRecovery_embedding_left S n H g A b e)

theorem fullLevelRecovery_embedding :
    (fullLevelRecovery S n H g A b e P eL Hm Hi hb N level).hom ≫
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n H g Hm Hi N).baseChange
        (y).left).embedding = e.hom ≫ ((Presentation.NativeHilbertAbelianLift.presentation S n H).baseChange b.left).embedding := by
  apply Over.OverMorphism.ext
  exact fullLevelRecovery_embedding_left S n H g A b e P eL Hm Hi hb N level

theorem fullLevelClassifier_markedSection (label : Multiplicative (Fin (2 * g) → ZMod N)) :
    (HilbertLevel.MarkedUniqueness.HilbertLevelPullback.markedPoint S n H g Hm Hi N y label).left =
      A.fullLevelGlobalSection level label ≫ e.hom.left ≫
        ((Presentation.NativeHilbertAbelianLift.presentation S n H).baseChange b.left).embedding.left :=
  (LevelReembedding.NativeHilbertFullLevelReembedding.recovery_markedSection S n H g Hm Hi A P c r rL hb N level label).trans
    (congrArg (fun f : A.scheme.left ⟶ (Projective.ProjectivePresentations.projectiveSpaceOver T.left n).left =>
      A.fullLevelGlobalSection level label ≫ f)
      (originalRecovery_embedding_left S n H g A b e))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.LevelRecovery.IntrinsicHilbertAbelianLift
