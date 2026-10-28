import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.PullbackAmbient
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.Transport

/-! # Pullback Affine Charts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.PullbackAffineCharts

noncomputable section

/-! Affine pullbacks of the embedded generated universal ideal recover the actual generated homogeneous projective ideal. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {n B N : ℕ} {r : ℕ → ℕ} {R : CommRingCat.{u}}
variable (x : Spec R ⟶ (Truncated.GeneratedParameters.truncatedGeneratedParameters S n B r N).left)

def generatedPullbackAffineChart : (Projective.ProjectivePresentations.affineProjectiveSpace R n).left ⟶
    (PullbackAmbient.generatedPullbackAmbient S n B r N).left :=
  pullback.lift (AffineProjective.Charts.affineProjectiveChartMap (x ≫ (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N).left) n)
    ((Projective.ProjectivePresentations.affineProjectiveSpace R n).hom ≫ x) (by
      rw [AffineProjective.Charts.affineProjectiveChartMap_over, Category.assoc])

theorem generatedPullbackAffineChart_fst : generatedPullbackAffineChart x ≫
    pullback.fst (Projective.ProjectivePresentations.projectiveSpaceOver
      (Truncated.GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S).left n).hom
        (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N).left =
      AffineProjective.Charts.affineProjectiveChartMap (x ≫ (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N).left) n :=
  pullback.lift_fst _ _ _

theorem generatedPullbackAffineChart_over :
    generatedPullbackAffineChart x ≫ (PullbackAmbient.generatedPullbackAmbient S n B r N).hom =
      (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom ≫ x := pullback.lift_snd _ _ _

theorem generatedPullbackAffineChart_isPullback :
    IsPullback (generatedPullbackAffineChart x) (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom
      (PullbackAmbient.generatedPullbackAmbient S n B r N).hom x := by
  let p := pullback.fst (Projective.ProjectivePresentations.projectiveSpaceOver
    (Truncated.GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S).left n).hom
      (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N).left
  have h : IsPullback (generatedPullbackAffineChart x ≫ p) (Projective.ProjectivePresentations.affineProjectiveSpace R n).hom
      (Projective.ProjectivePresentations.projectiveSpaceOver (Truncated.GradedParameters.truncatedGradedParameters (Fin (n + 1)) B r S).left n).hom
        (x ≫ (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N).left) := by
    rw [show generatedPullbackAffineChart x ≫ p =
      AffineProjective.Charts.affineProjectiveChartMap (x ≫ (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N).left) n from
        generatedPullbackAffineChart_fst x]
    exact AffineProjective.Charts.affineProjectiveChartMap_isPullback _ n
  exact h.of_right (generatedPullbackAffineChart_over x) (IsPullback.of_hasPullback _ _)

theorem generatedPullbackFlatFamily_affine_ideal (hB : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B) :
    ((PullbackAmbient.generatedPullbackFlatFamily S n B r N hB).ideal).comap (generatedPullbackAffineChart x) =
      (Truncated.AffineUniversalData.truncatedAffineUniversalData (x ≫ (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N).left)).projectiveIdeal := by
  rw [PullbackAmbient.generatedPullbackFlatFamily_ideal]
  exact ((Truncated.UniversalIdeal.truncatedUniversalIdeal S n B r).comap_comp (generatedPullbackAffineChart x) _).symm.trans
    ((congrArg (fun p => (Truncated.UniversalIdeal.truncatedUniversalIdeal S n B r).comap p)
      (generatedPullbackAffineChart_fst x)).trans (Truncated.UniversalIdeal.truncatedUniversalIdeal_comap S n B r _))

def generatedPullbackFamilyAtAffinePoint (hB : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B) :
    Closed.Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace R n) :=
  (PullbackAmbient.generatedPullbackFlatFamily S n B r N hB).pullbackAlong
    (generatedPullbackAffineChart x) x (generatedPullbackAffineChart_isPullback x)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.PullbackAffineCharts
