import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.PullbackParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.EmbeddingPullbackComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ClosedFamilyIntrinsicPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.BaseChangeNaturality

/-! # Projective Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.ProjectiveRecovery.HilbertLevelPullback

noncomputable section

/-! The existing full-level Hilbert universal family is the native
pullback of the original Hilbert universal family along its forgetful
map. The comparison preserves the existing projective presentation.
All subsequent base changes are arbitrary scheme morphisms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem comp_comp_eq
    {C : Type*} [Category* C] {W X Y Z : C}
    (a : W ⟶ X) (b : X ⟶ Y) (j : Y ⟶ Z) (i : X ⟶ Z) (k : W ⟶ Z)
    (hb : b ≫ j = i) (ha : a ≫ i = k) :
    (a ≫ b) ≫ j = k :=
  (Category.assoc _ _ _).trans ((congrArg (fun h => a ≫ h) hb).trans ha)

private theorem postcompose_inverse
    {C : Type*} [Category* C] {A B D E : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ E) (e : E ≅ D)
    (h : a ≫ b = c ≫ e.hom) : a ≫ (b ≫ e.inv) = c := by
  rw [← Category.assoc, h, Category.assoc, e.hom_inv_id, Category.comp_id]

private theorem embedding_left
    {S T : Scheme.{u}} {n : ℕ} {X : Over S}
    (j : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) (f : T ⟶ S) :
    (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding j f).left =
      ((Over.pullback f).map j).left ≫ (Projective.SpaceBaseChange.projectiveSpaceOverBaseChangeIso f n).inv.left := rfl

private theorem triangle_transfer
    {C : Type*} [Category* C] {X Y Z : C}
    (e e' : X ⟶ Y) (j j' : Y ⟶ Z) (i i' : X ⟶ Z)
    (he : e = e') (hj : j = j') (hi : i' = i) (h : e' ≫ j' = i') : e ≫ j = i :=
  (congrArg₂ (fun a b => a ≫ b) he hj).trans (h.trans hi)

private theorem presentationEmbedding_left
    {S T : Scheme.{u}} {n : ℕ} {X : Over S}
    (j : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j.left] (f : T ⟶ S)
    {Y : Over T} (a : Y ⟶ (Over.pullback f).obj X)
    (i : Y ⟶ Projective.ProjectivePresentations.projectiveSpaceOver T n)
    (h : a.left ≫ (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding j f).left = i.left) :
    let Q : Projective.ProjectivePresentations.ProjectivePresentation X := ⟨n, j, inferInstance⟩
    a.left ≫ (Q.baseChange f).embedding.left = i.left := by
  let Q : Projective.ProjectivePresentations.ProjectivePresentation X := ⟨n, j, inferInstance⟩
  have hj : (Q.baseChange f).embedding.left = (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding j f).left := rfl
  exact (congrArg (fun k => a.left ≫ k) hj).trans h

private theorem recoveryEmbedding_left
    {S T U : Scheme.{u}} {n : ℕ} {X : Over S} {Y : Over T}
    (j : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) (f : T ⟶ S)
    (i : Y ⟶ Projective.ProjectivePresentations.projectiveSpaceOver T n) (e : Y ≅ (Over.pullback f).obj X)
    (he : e.hom ≫ Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding j f = i) (g : U ⟶ T)
    (k : (Over.pullback g).obj Y ⟶ Projective.ProjectivePresentations.projectiveSpaceOver U n)
    (hk : Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding i g = k) :
    (Projective.EmbeddingPullbackComposition.ProjectivePullback.recoveryIso f e g).hom.left ≫
      (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding j (g ≫ f)).left = k.left :=
  congrArg Over.Hom.left (Projective.EmbeddingPullbackComposition.ProjectivePullback.recoveryIso_embedding_eq j f i e he g k hk)

private theorem isoTrans_hom_left {T : Scheme.{u}} {A B C : Over T}
    (e : A ≅ B) (k : B ≅ C) :
    (e ≪≫ k).hom.left = e.hom.left ≫ k.hom.left := rfl

private theorem isoTrans_triangle_left {T W : Scheme.{u}} {A B C : Over T}
    (e : A ≅ B) (k : B ≅ C) (j : C.left ⟶ W) (i : B.left ⟶ W) (l : A.left ⟶ W)
    (hk : k.hom.left ≫ j = i) (he : e.hom.left ≫ i = l) :
    (e ≪≫ k).hom.left ≫ j = l :=
  (congrArg (fun a => a ≫ j) (isoTrans_hom_left e k)).trans
    (comp_comp_eq e.hom.left k.hom.left j i l hk he)

private def relativeFamilyPullbackIso {S T : Scheme.{u}} {n : ℕ} {P : Polynomial ℚ}
    (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily S n P) (G : RelativeProjective.Families.RelativeProjectiveHilbertFamily T n P)
    (f : T ⟶ S) (h : F.pullback f = G) :
    G.family.scheme ≅ (Over.pullback f).obj F.family.scheme :=
  eqToIso (congrArg (fun H : RelativeProjective.Families.RelativeProjectiveHilbertFamily T n P => H.family.scheme) h.symm) ≪≫
    F.family.projectiveBaseChangeSchemeIso f

private theorem relativeFamilyNativePullback_embedding_left
    {S T : Scheme.{u}} {n : ℕ} {P : Polynomial ℚ}
    (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily S n P) (f : T ⟶ S) :
    (F.family.projectiveBaseChangeSchemeIso f).hom.left ≫
      (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding F.family.inclusion f).left =
        (F.pullback f).family.inclusion.left := by
  let k := F.family.projectiveBaseChangeSchemeIso f
  have hk' : k.hom.left ≫ (((Over.pullback f).map F.family.inclusion).left ≫
      (Projective.SpaceBaseChange.projectiveSpaceOverBaseChangeIso f n).inv.left) = (F.pullback f).family.inclusion.left :=
    congrArg Over.Hom.left (F.family.projectiveBaseChangeSchemeIso_embedding f)
  exact (congrArg (fun a => k.hom.left ≫ a) (embedding_left F.family.inclusion f)).trans hk'

private theorem relativeFamilyPullbackIso_embedding_left
    {S T : Scheme.{u}} {n : ℕ} {P : Polynomial ℚ}
    (F : RelativeProjective.Families.RelativeProjectiveHilbertFamily S n P) (G : RelativeProjective.Families.RelativeProjectiveHilbertFamily T n P)
    (f : T ⟶ S) (h : F.pullback f = G) :
    (relativeFamilyPullbackIso F G f h).hom.left ≫
      (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding F.family.inclusion f).left = G.family.inclusion.left := by
  cases h
  exact isoTrans_triangle_left (Iso.refl _) (F.family.projectiveBaseChangeSchemeIso f)
    _ _ _ (relativeFamilyNativePullback_embedding_left F f) (Category.id_comp _)

variable (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (P : Polynomial ℚ)
    (g : ℕ) (Pm Pi : Polynomial ℚ) (N : ℕ) [NeZero N]

private def fixedHilbertMap :
    (FixedDimension.Parameters.fixedDimensionHilbertParameter S n P g).left ⟶ (Hilbert.ParameterScheme.hilbertParameterScheme S n P).left :=
  (FixedDimension.Parameters.fixedDimensionHilbertParameterInclusion S n P g).left ≫
    (SmoothHilbert.Parameter.smoothHilbertParameterInclusion S n P).left

omit [AlgebraicGeometry.IsNoetherian S] in
private theorem fixedFamily_eq :
    FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily S n P g =
      (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).pullback (fixedHilbertMap S n P g) :=
  (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).pullback_comp
    (SmoothHilbert.Parameter.smoothHilbertParameterInclusion S n P).left
    (FixedDimension.Parameters.fixedDimensionHilbertParameterInclusion S n P g).left

private def fixedFamilyIso :
    (FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily S n P g).family.scheme ≅
      (Over.pullback (fixedHilbertMap S n P g)).obj (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme :=
  eqToIso (congrArg
    (fun F : RelativeProjective.Families.RelativeProjectiveHilbertFamily (FixedDimension.Parameters.fixedDimensionHilbertParameter S n P g).left n P =>
      F.family.scheme) (fixedFamily_eq S n P g)) ≪≫
    (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.projectiveBaseChangeSchemeIso (fixedHilbertMap S n P g)

omit [AlgebraicGeometry.IsNoetherian S] in
private theorem fixedFamilyIso_eq :
    fixedFamilyIso S n P g =
      relativeFamilyPullbackIso (Hilbert.ParameterScheme.hilbertUniversalFamily S n P)
        (FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily S n P g) (fixedHilbertMap S n P g)
        (fixedFamily_eq S n P g).symm := rfl

omit [AlgebraicGeometry.IsNoetherian S] in
private theorem fixedFamilyIso_embedding_left :
    (fixedFamilyIso S n P g).hom.left ≫
      (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion
        (fixedHilbertMap S n P g)).left =
      (FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n P g).embedding.left := by
  rw [fixedFamilyIso_eq]
  exact relativeFamilyPullbackIso_embedding_left (Hilbert.ParameterScheme.hilbertUniversalFamily S n P)
    (FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily S n P g) (fixedHilbertMap S n P g)
    (fixedFamily_eq S n P g).symm

omit [AlgebraicGeometry.IsNoetherian S] in
private theorem fixedFamilyIso_embedding :
    (fixedFamilyIso S n P g).hom ≫
      Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion
        (fixedHilbertMap S n P g) =
      (FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n P g).embedding := by
  apply Over.OverMorphism.ext
  exact fixedFamilyIso_embedding_left S n P g

private def groupHilbertMap :
    (FixedDimension.GroupParameters.fixedDimensionHilbertGroupRelativeParameter S n P g Pm Pi).left ⟶ (Hilbert.ParameterScheme.hilbertParameterScheme S n P).left :=
  (FixedDimension.GroupParameters.fixedDimensionHilbertGroupRelativeParameter S n P g Pm Pi).hom ≫ fixedHilbertMap S n P g

private def groupFamilyIso :
    FixedDimension.GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi ≅
      (Over.pullback (groupHilbertMap S n P g Pm Pi)).obj (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme :=
  Projective.EmbeddingPullbackComposition.ProjectivePullback.recoveryIso (fixedHilbertMap S n P g) (fixedFamilyIso S n P g)
    (FixedDimension.GroupParameters.fixedDimensionHilbertGroupRelativeParameter S n P g Pm Pi).hom

private theorem groupFamilyIso_eq :
    groupFamilyIso S n P g Pm Pi =
      Projective.EmbeddingPullbackComposition.ProjectivePullback.recoveryIso (fixedHilbertMap S n P g) (fixedFamilyIso S n P g)
        (FixedDimension.GroupParameters.fixedDimensionHilbertGroupRelativeParameter S n P g Pm Pi).hom := rfl

private theorem groupPresentation_embedding :
    Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding (FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n P g).embedding
        (FixedDimension.GroupParameters.fixedDimensionHilbertGroupRelativeParameter S n P g Pm Pi).hom =
      (FixedDimension.GroupGlobalParameter.fixedDimensionHilbertGroupUniversalProjectivePresentation S n P g Pm Pi).embedding :=
  Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding_baseChange (FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n P g)
    (FixedDimension.GroupParameters.fixedDimensionHilbertGroupRelativeParameter S n P g Pm Pi).hom

private theorem groupFamilyIso_embedding :
    (groupFamilyIso S n P g Pm Pi).hom ≫
      Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion
        (groupHilbertMap S n P g Pm Pi) =
      (FixedDimension.GroupGlobalParameter.fixedDimensionHilbertGroupUniversalProjectivePresentation S n P g Pm Pi).embedding := by
  apply Over.OverMorphism.ext
  rw [groupFamilyIso_eq]
  exact recoveryEmbedding_left (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion
    (fixedHilbertMap S n P g)
    (FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n P g).embedding
    (fixedFamilyIso S n P g) (fixedFamilyIso_embedding S n P g)
    (FixedDimension.GroupParameters.fixedDimensionHilbertGroupRelativeParameter S n P g Pm Pi).hom
    (FixedDimension.GroupGlobalParameter.fixedDimensionHilbertGroupUniversalProjectivePresentation S n P g Pm Pi).embedding
    (groupPresentation_embedding S n P g Pm Pi)

private def abelianBaseMap :
    (FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi).left ⟶
      (FixedDimension.GroupParameters.fixedDimensionHilbertGroupRelativeParameter S n P g Pm Pi).left :=
  (FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameterInclusion S n P g Pm Pi).left

private def abelianHilbertMap :
    (FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi).left ⟶ (Hilbert.ParameterScheme.hilbertParameterScheme S n P).left :=
  (abelianBaseMap S n P g Pm Pi) ≫
    groupHilbertMap S n P g Pm Pi

private def abelianFamilyIso :
    (FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n P g Pm Pi).scheme ≅
      (Over.pullback (abelianHilbertMap S n P g Pm Pi)).obj (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme :=
  Projective.EmbeddingPullbackComposition.ProjectivePullback.recoveryIso (groupHilbertMap S n P g Pm Pi) (groupFamilyIso S n P g Pm Pi)
    (abelianBaseMap S n P g Pm Pi)

private theorem abelianFamilyIso_eq :
    abelianFamilyIso S n P g Pm Pi =
      Projective.EmbeddingPullbackComposition.ProjectivePullback.recoveryIso (groupHilbertMap S n P g Pm Pi) (groupFamilyIso S n P g Pm Pi)
        (abelianBaseMap S n P g Pm Pi) := rfl

private theorem abelianPresentation_embedding :
    Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding (FixedDimension.GroupGlobalParameter.fixedDimensionHilbertGroupUniversalProjectivePresentation S n P g Pm Pi).embedding
        (abelianBaseMap S n P g Pm Pi) =
      (FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).embedding :=
  Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding_baseChange (FixedDimension.GroupGlobalParameter.fixedDimensionHilbertGroupUniversalProjectivePresentation S n P g Pm Pi)
    (abelianBaseMap S n P g Pm Pi)

private theorem abelianRecovery_embedding_left :
    (Projective.EmbeddingPullbackComposition.ProjectivePullback.recoveryIso (groupHilbertMap S n P g Pm Pi) (groupFamilyIso S n P g Pm Pi)
      (abelianBaseMap S n P g Pm Pi)).hom.left ≫
      (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion
        ((abelianBaseMap S n P g Pm Pi) ≫
          groupHilbertMap S n P g Pm Pi)).left =
      (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding
        (FixedDimension.GroupGlobalParameter.fixedDimensionHilbertGroupUniversalProjectivePresentation S n P g Pm Pi).embedding
        (abelianBaseMap S n P g Pm Pi)).left :=
  congrArg Over.Hom.left
    (Projective.EmbeddingPullbackComposition.ProjectivePullback.recoveryIso_embedding (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion
      (groupHilbertMap S n P g Pm Pi)
      (FixedDimension.GroupGlobalParameter.fixedDimensionHilbertGroupUniversalProjectivePresentation S n P g Pm Pi).embedding
      (groupFamilyIso S n P g Pm Pi) (groupFamilyIso_embedding S n P g Pm Pi)
      (abelianBaseMap S n P g Pm Pi))

private theorem abelianFamilyIso_hom_left :
    (abelianFamilyIso S n P g Pm Pi).hom.left =
      (Projective.EmbeddingPullbackComposition.ProjectivePullback.recoveryIso (groupHilbertMap S n P g Pm Pi) (groupFamilyIso S n P g Pm Pi)
        (abelianBaseMap S n P g Pm Pi)).hom.left := rfl

private theorem abelianHilbertEmbedding_left :
    (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion
      (abelianHilbertMap S n P g Pm Pi)).left =
      (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion
        ((abelianBaseMap S n P g Pm Pi) ≫
          groupHilbertMap S n P g Pm Pi)).left := rfl

private theorem abelianPresentation_embedding_left :
    (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding
      (FixedDimension.GroupGlobalParameter.fixedDimensionHilbertGroupUniversalProjectivePresentation S n P g Pm Pi).embedding
      (abelianBaseMap S n P g Pm Pi)).left =
      (FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).embedding.left :=
  congrArg Over.Hom.left (abelianPresentation_embedding S n P g Pm Pi)

private theorem abelianFamilyIso_embedding_left :
    (abelianFamilyIso S n P g Pm Pi).hom.left ≫
      (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion
        (abelianHilbertMap S n P g Pm Pi)).left =
      (FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).embedding.left :=
  triangle_transfer _ _ _ _ _ _ (abelianFamilyIso_hom_left S n P g Pm Pi)
    (abelianHilbertEmbedding_left S n P g Pm Pi) (abelianPresentation_embedding_left S n P g Pm Pi)
    (abelianRecovery_embedding_left S n P g Pm Pi)

private theorem abelianFamilyIso_embedding :
    (abelianFamilyIso S n P g Pm Pi).hom ≫
      Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion
        (abelianHilbertMap S n P g Pm Pi) =
      (FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).embedding := by
  apply Over.OverMorphism.ext
  exact abelianFamilyIso_embedding_left S n P g Pm Pi

/-- The actual full-level universal abelian family lies over the original
Hilbert family along the specified forgetful map. -/
def universalFamilyIso :
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S n P g Pm Pi N).scheme ≅
      (Over.pullback (PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N).left).obj (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme :=
  Projective.EmbeddingPullbackComposition.ProjectivePullback.recoveryIso (abelianHilbertMap S n P g Pm Pi)
    (abelianFamilyIso S n P g Pm Pi)
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelRelativeParameter S n P g Pm Pi N).hom

private theorem universalFamilyIso_eq :
    universalFamilyIso S n P g Pm Pi N =
      Projective.EmbeddingPullbackComposition.ProjectivePullback.recoveryIso (abelianHilbertMap S n P g Pm Pi)
        (abelianFamilyIso S n P g Pm Pi)
        (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelRelativeParameter S n P g Pm Pi N).hom := rfl

private theorem fullLevelPresentation_embedding :
    Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding (FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).embedding
        (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelRelativeParameter S n P g Pm Pi N).hom =
      (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N).embedding :=
  Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding_baseChange (FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi)
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelRelativeParameter S n P g Pm Pi N).hom

private theorem universalFamilyIso_embedding_native :
    (universalFamilyIso S n P g Pm Pi N).hom ≫
      Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion
        (PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N).left =
      (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N).embedding := by
  apply Over.OverMorphism.ext
  rw [universalFamilyIso_eq]
  exact recoveryEmbedding_left (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion
    (abelianHilbertMap S n P g Pm Pi)
    (FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).embedding
    (abelianFamilyIso S n P g Pm Pi) (abelianFamilyIso_embedding S n P g Pm Pi)
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelRelativeParameter S n P g Pm Pi N).hom
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N).embedding
    (fullLevelPresentation_embedding S n P g Pm Pi N)

private theorem universalFamilyIso_embedding_native_left :
    (universalFamilyIso S n P g Pm Pi N).hom.left ≫
      (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion
        (PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N).left).left =
      (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N).embedding.left :=
  congrArg Over.Hom.left (universalFamilyIso_embedding_native S n P g Pm Pi N)

/-- Compatibility with the original Hilbert inclusion and the existing
full-level universal projective presentation. -/
theorem universalFamilyIso_embedding :
    let Q : Projective.ProjectivePresentations.ProjectivePresentation (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme :=
      ⟨n, (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion, inferInstance⟩
    (universalFamilyIso S n P g Pm Pi N).hom ≫
      (Q.baseChange (PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N).left).embedding =
      (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N).embedding := by
  apply Over.OverMorphism.ext
  exact presentationEmbedding_left (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion
    (PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N).left
    (universalFamilyIso S n P g Pm Pi N).hom
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N).embedding
    (universalFamilyIso_embedding_native_left S n P g Pm Pi N)

/-- The same comparison over every test scheme of the full-level parameter. -/
def universalFamilyPullbackIso {T : Scheme.{u}}
    (b : T ⟶ (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N).left) :
    ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalAbelianScheme S n P g Pm Pi N).pullback b).scheme ≅
      (Over.pullback (b ≫ (PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N).left)).obj
        (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme :=
  Projective.EmbeddingPullbackComposition.ProjectivePullback.recoveryIso (PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N).left
    (universalFamilyIso S n P g Pm Pi N) b

private theorem universalFamilyPullbackIso_eq {T : Scheme.{u}}
    (b : T ⟶ (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N).left) :
    universalFamilyPullbackIso S n P g Pm Pi N b =
      Projective.EmbeddingPullbackComposition.ProjectivePullback.recoveryIso (PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N).left
        (universalFamilyIso S n P g Pm Pi N) b := rfl

private theorem universalFamilyPullbackIso_embedding_native {T : Scheme.{u}}
    (b : T ⟶ (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N).left) :
    (universalFamilyPullbackIso S n P g Pm Pi N b).hom ≫
      Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion
        (b ≫ (PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N).left) =
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N).baseChange b).embedding := by
  apply Over.OverMorphism.ext
  rw [universalFamilyPullbackIso_eq]
  exact recoveryEmbedding_left (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion
    (PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N).left
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N).embedding
    (universalFamilyIso S n P g Pm Pi N) (universalFamilyIso_embedding_native S n P g Pm Pi N) b
    ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N).baseChange b).embedding
    (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding_baseChange
      (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N) b)

private theorem universalFamilyPullbackIso_embedding_native_left {T : Scheme.{u}}
    (b : T ⟶ (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N).left) :
    (universalFamilyPullbackIso S n P g Pm Pi N b).hom.left ≫
      (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion
        (b ≫ (PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N).left)).left =
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N).baseChange b).embedding.left :=
  congrArg Over.Hom.left (universalFamilyPullbackIso_embedding_native S n P g Pm Pi N b)

theorem universalFamilyPullbackIso_embedding_left {T : Scheme.{u}}
    (b : T ⟶ (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N).left) :
    let Q : Projective.ProjectivePresentations.ProjectivePresentation (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme :=
      ⟨n, (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion, inferInstance⟩
    (universalFamilyPullbackIso S n P g Pm Pi N b).hom.left ≫
      (Q.baseChange (b ≫ (PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N).left)).embedding.left =
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N).baseChange b).embedding.left := by
  exact presentationEmbedding_left (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion
    (b ≫ (PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N).left)
    (universalFamilyPullbackIso S n P g Pm Pi N b).hom
    ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N).baseChange b).embedding
    (universalFamilyPullbackIso_embedding_native_left S n P g Pm Pi N b)

theorem universalFamilyPullbackIso_embedding {T : Scheme.{u}}
    (b : T ⟶ (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N).left) :
    let Q : Projective.ProjectivePresentations.ProjectivePresentation (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.scheme :=
      ⟨n, (Hilbert.ParameterScheme.hilbertUniversalFamily S n P).family.inclusion, inferInstance⟩
    (universalFamilyPullbackIso S n P g Pm Pi N b).hom ≫
      (Q.baseChange (b ≫ (PullbackParameter.HilbertLevelPullback.forget S n P g Pm Pi N).left)).embedding =
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N).baseChange b).embedding := by
  apply Over.OverMorphism.ext
  exact universalFamilyPullbackIso_embedding_left S n P g Pm Pi N b

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.ProjectiveRecovery.HilbertLevelPullback
