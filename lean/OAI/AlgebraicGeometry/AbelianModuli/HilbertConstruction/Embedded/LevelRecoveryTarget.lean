import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.LevelRecoveryTransfer

/-! # Level Recovery Target -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.LevelRecoveryTarget

noncomputable section

/-! Keep the target family and its original embedding together when
transporting a full-level recovery across an equality of presentations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

structure EmbeddedFullLevelTarget (S : Scheme.{u}) (g N : ℕ) (Z : Over S) where
  family : Level.Data.AbelianSchemeWithFullLevel g N S
  embedding : family.abelian.scheme ⟶ Z

theorem EmbeddedFullLevelTarget.eq_of_family_embedding_left
    {S : Scheme.{u}} {g N : ℕ} {Z : Over S}
    {K L : EmbeddedFullLevelTarget S g N Z}
    (h : K.family = L.family) (he : HEq K.embedding.left L.embedding.left) : K = L := by
  cases K with
  | mk F i =>
    cases L with
    | mk G j =>
      cases h
      have hi : i = j := Over.OverMorphism.ext (eq_of_heq he)
      cases hi
      rfl

def EmbeddedFullLevelTarget.Recovery {S : Scheme.{u}} {g N : ℕ} {Z : Over S}
    (K : EmbeddedFullLevelTarget S g N Z)
    (A : Abelian.Schemes.AbelianScheme g S) (l : A.FullLevel N) (k : A.scheme ⟶ Z) : Prop :=
  LevelIso.EmbeddedFullLevelRecovery A l K.family k K.embedding

theorem EmbeddedFullLevelTarget.changeTarget {S : Scheme.{u}} {g N : ℕ} {Z : Over S}
    {K L : EmbeddedFullLevelTarget S g N Z}
    (h : K = L) {A : Abelian.Schemes.AbelianScheme g S} {l : A.FullLevel N} {k : A.scheme ⟶ Z}
    (r : K.Recovery A l k) : L.Recovery A l k := by
  cases h
  exact r

def iteratedEmbeddedFullLevelTarget
    {S B C T : Scheme.{u}} {g N : ℕ} (F : Level.Data.AbelianSchemeWithFullLevel g N S)
    (P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme)
    (p : B ⟶ S) (q : C ⟶ B) (a : T ⟶ C) :
    EmbeddedFullLevelTarget T g N (Projective.ProjectivePresentations.projectiveSpaceOver T P.dimension) where
  family := ((F.pullback p).pullback q).pullback a
  embedding := (LevelIso.fullLevelProjectiveBaseChange ((F.pullback p).pullback q)
    (LevelIso.fullLevelProjectiveBaseChange (F.pullback p)
      (LevelIso.fullLevelProjectiveBaseChange F P p) q) a).embedding

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.LevelRecoveryTarget
