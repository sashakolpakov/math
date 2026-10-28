import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.LevelRecoveryData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.LevelRecoveryTransfer

/-! # Level Embedded Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic

noncomputable section

/-! View the original native Hilbert recovery as an embedded full-level
isomorphism. The underlying isomorphism and all of its laws are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

def LevelRecoveryData.NativeFullLevelRecoveryData.embeddedIso
    {S : Scheme.{u}} [IsNoetherian S] {n : ℕ} {H : Polynomial ℚ}
    {g : ℕ} {Hm Hi : Polynomial ℚ} {N : ℕ} [NeZero N]
    {T : Over S} {A : Abelian.Schemes.AbelianScheme g T.left} {level : A.FullLevel N}
    {b : T ⟶ Hilbert.ParameterScheme.hilbertParameterScheme S n H}
    {k : A.scheme.left ⟶ (Projective.ProjectivePresentations.projectiveSpaceOver T.left n).left}
    (data : LevelRecoveryData.NativeFullLevelRecoveryData S n H g Hm Hi N T A level b k) :
    Embedded.LevelIso.EmbeddedFullLevelIso A
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalFamily S n H g Hm Hi N).pullback data.point.left).abelian
      level ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalFamily S n H g Hm Hi N).pullback data.point.left).level
      k (Embedded.LevelIso.fullLevelProjectiveBaseChange
        (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalFamily S n H g Hm Hi N)
        (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n H g Hm Hi N)
        data.point.left).embedding.left where
  iso := data.iso
  group := data.group
  level_eq := data.level_eq
  embedding_eq := data.embedding_eq

theorem LevelRecoveryData.NativeFullLevelRecoveryData.iteratedRecovery
    {S : Scheme.{u}} [IsNoetherian S] {n : ℕ} {H : Polynomial ℚ}
    {g : ℕ} {Hm Hi : Polynomial ℚ} {N : ℕ} [NeZero N]
    {T : Over S} {A : Abelian.Schemes.AbelianScheme g T.left} {level : A.FullLevel N}
    {b : T ⟶ Hilbert.ParameterScheme.hilbertParameterScheme S n H}
    {k : A.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver T.left n}
    (data : LevelRecoveryData.NativeFullLevelRecoveryData S n H g Hm Hi N T A level b k.left)
    {B C : Scheme.{u}}
    {p : B ⟶ (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n H g Hm Hi N).left}
    {q : C ⟶ B} {a : T.left ⟶ C}
    (h : Embedded.LevelIso.IteratedFullLevelFamilyRecovery
      (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalFamily S n H g Hm Hi N)
      (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n H g Hm Hi N)
      p q data.point.left a) :
    Embedded.LevelIso.EmbeddedFullLevelRecovery A level
      ((((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalFamily S n H g Hm Hi N).pullback p).pullback q).pullback a)
      k (Embedded.LevelIso.fullLevelProjectiveBaseChange
        (((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalFamily S n H g Hm Hi N).pullback p).pullback q)
        (Embedded.LevelIso.fullLevelProjectiveBaseChange
          ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalFamily S n H g Hm Hi N).pullback p)
          (Embedded.LevelIso.fullLevelProjectiveBaseChange
            (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalFamily S n H g Hm Hi N)
            (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n H g Hm Hi N) p) q) a).embedding :=
  h.applyIso data.embeddedIso

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic
