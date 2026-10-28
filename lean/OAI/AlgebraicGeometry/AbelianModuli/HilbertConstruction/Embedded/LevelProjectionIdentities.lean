import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.LevelRecoveryTarget

/-! # Level Projection Identities -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.LevelProjectionIdentities

noncomputable section

/-! Native scheme projections of the original full-level embedding
wrappers, before specialization to a concrete parameter family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem abelianProjectiveBaseChangeEmbedding_left
    {S T : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme) (f : T ⟶ S) :
    HEq (LevelIso.abelianProjectiveBaseChangeEmbedding A P f).left
      (P.baseChange f).embedding.left := by
  rfl

theorem projectivePresentation_baseChange_embedding_left_heq
    {S T : Scheme.{u}} {X : Over S} {P Q : Projective.ProjectivePresentations.ProjectivePresentation X}
    (h : P = Q) (f : T ⟶ S) :
    HEq (P.baseChange f).embedding.left (Q.baseChange f).embedding.left := by
  cases h
  rfl

private theorem fullLevelProjectiveBaseChange_eq
    {S T : Scheme.{u}} {g N : ℕ} (F : Level.Data.AbelianSchemeWithFullLevel g N S)
    (P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme) (f : T ⟶ S) :
    LevelIso.fullLevelProjectiveBaseChange F P f = P.baseChange f := rfl

private theorem projectiveBaseChangeTwiceEmbedding_heq
    {S T U : Scheme.{u}} {X : Over S} {P Q : Projective.ProjectivePresentations.ProjectivePresentation X}
    (h : P = Q) (f : T ⟶ S) (a : U ⟶ T) :
    HEq ((P.baseChange f).baseChange a).embedding.left
      ((Q.baseChange f).baseChange a).embedding.left := by
  cases h
  rfl

private theorem iteratedEmbeddedFullLevelTarget_embedding_unfold
    {S B C T : Scheme.{u}} {g N : ℕ} (F : Level.Data.AbelianSchemeWithFullLevel g N S)
    (P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme)
    (p : B ⟶ S) (q : C ⟶ B) (a : T ⟶ C) :
    HEq (LevelRecoveryTarget.iteratedEmbeddedFullLevelTarget F P p q a).embedding.left
      (LevelIso.fullLevelProjectiveBaseChange ((F.pullback p).pullback q)
        (LevelIso.fullLevelProjectiveBaseChange (F.pullback p)
          (LevelIso.fullLevelProjectiveBaseChange F P p) q) a).embedding.left := by
  rfl

theorem iteratedEmbeddedFullLevelTarget_embedding_left
    {S B C T : Scheme.{u}} {g N : ℕ} (F : Level.Data.AbelianSchemeWithFullLevel g N S)
    (P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme)
    (p : B ⟶ S) (q : C ⟶ B) (a : T ⟶ C) :
    HEq (LevelRecoveryTarget.iteratedEmbeddedFullLevelTarget F P p q a).embedding.left
      (((P.baseChange p).baseChange q).baseChange a).embedding.left := by
  let P₁ := LevelIso.fullLevelProjectiveBaseChange F P p
  let P₂ := LevelIso.fullLevelProjectiveBaseChange (F.pullback p) P₁ q
  have h₁ := fullLevelProjectiveBaseChange_eq F P p
  have h₂ := fullLevelProjectiveBaseChange_eq (F.pullback p) P₁ q
  have h₃ := fullLevelProjectiveBaseChange_eq ((F.pullback p).pullback q) P₂ a
  have h₃' : HEq (LevelIso.fullLevelProjectiveBaseChange ((F.pullback p).pullback q) P₂ a).embedding.left
      (P₂.baseChange a).embedding.left := by
    cases h₃
    rfl
  exact (iteratedEmbeddedFullLevelTarget_embedding_unfold F P p q a).trans
    (h₃'.trans ((projectivePresentation_baseChange_embedding_left_heq h₂ a).trans
      (projectiveBaseChangeTwiceEmbedding_heq h₁ q a)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.LevelProjectionIdentities
