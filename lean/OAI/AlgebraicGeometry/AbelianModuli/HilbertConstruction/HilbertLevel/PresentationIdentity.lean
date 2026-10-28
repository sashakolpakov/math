import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.PullbackParameter

/-! # Presentation Identity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.PresentationIdentity

noncomputable section

/-! The actual full-level Hilbert presentation is the original base
change; its equality can be carried through further pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem HilbertFullLevelPullback.projective_eq_native
    (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (H : Polynomial ℚ)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (Z : Over S) (c : Z ⟶ Hilbert.ParameterScheme.hilbertParameterScheme S n H) :
    PullbackParameter.HilbertLevelPullback.projective S n H g Hm Hi N Z c =
      (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n H g Hm Hi N).baseChange
        (PullbackParameter.HilbertLevelPullback.toFullLevel S n H g Hm Hi N Z c).left := rfl

theorem projectiveBaseChangeTwiceEmbedding_heq
    {S T U : Scheme.{u}} {X : Over S}
    {P Q : Projective.ProjectivePresentations.ProjectivePresentation X} (h : P = Q) (f : T ⟶ S) (a : U ⟶ T) :
    HEq (((P.baseChange f).baseChange a).embedding.left)
      (((Q.baseChange f).baseChange a).embedding.left) := by
  cases h
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.PresentationIdentity
