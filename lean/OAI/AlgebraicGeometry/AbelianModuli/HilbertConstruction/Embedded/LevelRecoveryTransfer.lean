import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.LevelIso

/-! # Level Recovery Transfer -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded

noncomputable section

/-! Apply a two-stage family recovery to an original embedded family
before specializing any of the parameter schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem LevelIso.EmbeddedFullLevelRecovery.change_embedding_left
    {S : Scheme.{u}} {g N : ℕ}
    {A : Abelian.Schemes.AbelianScheme g S} {level : A.FullLevel N}
    {F : Level.Data.AbelianSchemeWithFullLevel g N S} {Z : Over S}
    {i i' : A.scheme ⟶ Z} {j : F.abelian.scheme ⟶ Z}
    (E : LevelIso.EmbeddedFullLevelRecovery A level F i j) (h : i.left = i'.left) :
    LevelIso.EmbeddedFullLevelRecovery A level F i' j := by
  have hi : i = i' := Over.OverMorphism.ext h
  cases hi
  exact E

theorem LevelIso.IteratedFullLevelFamilyRecovery.applyIso
    {S B C T : Scheme.{u}} {g N : ℕ}
    {F : Level.Data.AbelianSchemeWithFullLevel g N S}
    {P : Projective.ProjectivePresentations.ProjectivePresentation F.abelian.scheme}
    {p : B ⟶ S} {q : C ⟶ B} {y : T ⟶ S} {a : T ⟶ C}
    (h : LevelIso.IteratedFullLevelFamilyRecovery F P p q y a)
    {A : Abelian.Schemes.AbelianScheme g T} {l : A.FullLevel N}
    {k : A.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver T P.dimension}
    (E : LevelIso.EmbeddedFullLevelIso A (F.pullback y).abelian l (F.pullback y).level
      k.left (LevelIso.fullLevelProjectiveBaseChange F P y).embedding.left) :
    LevelIso.EmbeddedFullLevelRecovery A l (((F.pullback p).pullback q).pullback a) k
      (LevelIso.fullLevelProjectiveBaseChange ((F.pullback p).pullback q)
        (LevelIso.fullLevelProjectiveBaseChange (F.pullback p)
          (LevelIso.fullLevelProjectiveBaseChange F P p) q) a).embedding := by
  exact (@h A l E.iso E.group E.level_eq).change_embedding_left E.embedding_eq

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded
