import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GeneratedFamily

/-! # Pullback Ambient -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.PullbackAmbient

noncomputable section

/-! The generated universal family as a closed family in the pulled-back projective ambient, with its defining ideal expressed by actual ideal pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable (S : Scheme.{u}) (n B : ℕ) (r : ℕ → ℕ) (N : ℕ)

def generatedPullbackAmbient : Over (Truncated.GeneratedParameters.truncatedGeneratedParameters S n B r N).left :=
  (Over.pullback (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N).left).obj
    (Projective.ProjectivePresentations.projectiveSpaceOver (Truncated.GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S).left n)

def generatedPullbackEmbedding : Truncated.GeneratedFamily.truncatedGeneratedFamily S n B r N ⟶ generatedPullbackAmbient S n B r N :=
  (Over.pullback (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N).left).map (Truncated.UniversalIdeal.truncatedUniversalEmbedding S n B r)

instance generatedPullbackEmbedding_closed : IsClosedImmersion (generatedPullbackEmbedding S n B r N).left :=
  Projective.PresentationBaseChange.overPullback_map_closed (Truncated.UniversalIdeal.truncatedUniversalEmbedding S n B r) (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N).left

def generatedPullbackFlatFamily (hB : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B) :
    Closed.Families.FlatClosedFamily (generatedPullbackAmbient S n B r N) := by
  have : Flat (Truncated.GeneratedFamily.truncatedGeneratedFamily S n B r N).hom := Truncated.GeneratedFamily.truncatedGeneratedFamily_flat hB
  have : LocallyOfFinitePresentation (Truncated.GeneratedFamily.truncatedGeneratedFamily S n B r N).hom :=
    Truncated.GeneratedFamily.truncatedGeneratedFamily_locallyFinitePresentation S n B r N
  exact Closed.Families.FlatClosedFamily.ofEmbedding (generatedPullbackEmbedding S n B r N)

theorem generatedPullbackFlatFamily_ideal (hB : Truncated.FinitePersistence.truncatedFlatnessBound n N ≤ B) :
    (generatedPullbackFlatFamily S n B r N hB).ideal =
      (Truncated.UniversalIdeal.truncatedUniversalIdeal S n B r).comap
        (pullback.fst (Projective.ProjectivePresentations.projectiveSpaceOver
          (Truncated.GradedParameters.truncatedGradedParameters.{u, 0} (Fin (n + 1)) B r S).left n).hom
            (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N).left) := by
  have h := Projective.IdealBaseChange.closedImmersion_kernel_isPullback _ _ _ _
    (Projective.PresentationBaseChange.overPullback_map_isPullback (Truncated.UniversalIdeal.truncatedUniversalEmbedding S n B r)
      (Truncated.GeneratedParameters.truncatedGeneratedInclusion S n B r N).left)
  have he : (Truncated.UniversalIdeal.truncatedUniversalEmbedding S n B r).left.ker = Truncated.UniversalIdeal.truncatedUniversalIdeal S n B r :=
    (Truncated.UniversalIdeal.truncatedUniversalIdeal S n B r).ker_subschemeι
  rw [he] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.PullbackAmbient
