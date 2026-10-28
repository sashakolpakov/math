import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.LevelDataRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ParameterPullbackCompatibility

/-! # Data Embedding Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.DataEmbeddingRecovery

noncomputable section

/-! The native Hilbert point/data recovery isomorphisms preserve the
existing projective embeddings. These statements expose the embedding
compatibility needed to transport actual marked sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

private theorem triangle_transfer {C : Type*} [Category* C] {X Y Z : C}
    (e e' : X ⟶ Y) (j j' : Y ⟶ Z) (i i' : X ⟶ Z)
    (he : e = e') (hj : j = j') (hi : i' = i) (h : e' ≫ j' = i') : e ≫ j = i :=
  (congrArg₂ (fun a b => a ≫ b) he hj).trans (h.trans hi)

private theorem compose_triangles {C : Type*} [Category* C] {W X Y Z : C}
    (e : W ⟶ X) (k : X ⟶ Y) (j : Y ⟶ Z) (r : X ⟶ Z) (s : W ⟶ Z)
    (hk : k ≫ j = r) (he : e ≫ r = s) : (e ≫ k) ≫ j = s :=
  (Category.assoc _ _ _).trans ((congrArg (fun a => e ≫ a) hk).trans he)

private theorem triangle_of_left_eq {C : Type*} [Category* C] {X Y Z : C}
    (e e' : X ⟶ Y) (j : Y ⟶ Z) (i : X ⟶ Z) (he : e = e') (h : e' ≫ j = i) :
    e ≫ j = i :=
  (congrArg (fun a => a ≫ j) he).trans h

private theorem dependent_congr {I : Type*} {F : I → Type*}
    (f : (i : I) → F i) {i j : I} (h : i = j) : HEq (f i) (f j) := by
  cases h
  rfl

private theorem twicePresentationEmbedding_left
    {B V W : Scheme.{u}} {X : Over B} (P : Projective.ProjectivePresentations.ProjectivePresentation X)
    (f : V ⟶ B) (h : W ⟶ V) :
    ((P.baseChange f).baseChange h).embedding.left =
      (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding P.embedding f) h).left := rfl

private theorem abelian_eqSchemeIso_embedding_left
    {B : Scheme.{u}} {g n : ℕ} {I : Type*} (A : I → Abelian.Schemes.AbelianScheme g B)
    (j : ∀ i, (A i).scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver B n) {i k : I} (h : i = k) :
    (Abelian.Schemes.AbelianScheme.eqSchemeIso (congrArg A h)).hom.left ≫ (j k).left = (j i).left := by
  cases h
  exact Category.id_comp _

private theorem fullLevel_eqSchemeIso_embedding_left
    {B : Scheme.{u}} {g n N : ℕ} {I : Type*} (A : I → Level.Data.AbelianSchemeWithFullLevel g N B)
    (j : ∀ i, (A i).abelian.scheme ⟶ Projective.ProjectivePresentations.projectiveSpaceOver B n) {i k : I} (h : i = k) :
    (Level.Data.AbelianSchemeWithFullLevel.eqSchemeIso (congrArg A h)).hom.left ≫ (j k).left = (j i).left := by
  cases h
  exact Category.id_comp _

variable (S : Scheme.{u}) [IsNoetherian S] (n : ℕ) (P : Polynomial ℚ)
    (g : ℕ) (Pm Pi : Polynomial ℚ)

local instance embeddingRecoveryUniversalGroup :
    GrpObj (FixedDimension.GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi) :=
  FixedDimension.GroupParameters.fixedDimensionHilbertGroupUniversalGroupObj S n P g Pm Pi

private theorem groupPointIso_left {T : Over S}
    (y : T ⟶ FixedDimension.GroupGlobalParameter.fixedDimensionHilbertGroupParameter S n P g Pm Pi) :
    (GroupUniversalRecovery.fixedDimensionHilbertGroupPointFamilyIso S n P g Pm Pi y).hom.left =
      (Single.ParameterBaseChange.singleParameterBaseChangeIso (GroupUniversalRecovery.fixedDimensionHilbertGroupPointRelativeMap S n P g Pm Pi y)
        (FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily S n P g).family.scheme).inv.left := rfl

private theorem groupPointEmbedding_left {T : Over S}
    (y : T ⟶ FixedDimension.GroupGlobalParameter.fixedDimensionHilbertGroupParameter S n P g Pm Pi) :
    ((FixedDimension.GroupPointData.fixedDimensionHilbertGroupPointEquiv S n P g Pm Pi T y).projective S n P g Pm Pi).embedding.left =
      ((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n P g).baseChange
        (FixedDimension.GroupPointData.fixedDimensionHilbertGroupPointEquiv S n P g Pm Pi T y).1.left).embedding.left := rfl

private theorem groupUniversalEmbedding_left {T : Over S}
    (y : T ⟶ FixedDimension.GroupGlobalParameter.fixedDimensionHilbertGroupParameter S n P g Pm Pi) :
    (((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n P g).baseChange
      (FixedDimension.GroupParameters.fixedDimensionHilbertGroupRelativeParameter S n P g Pm Pi).hom).baseChange
      (GroupUniversalRecovery.fixedDimensionHilbertGroupPointRelativeMap S n P g Pm Pi y).left).embedding.left =
      ((FixedDimension.GroupGlobalParameter.fixedDimensionHilbertGroupUniversalProjectivePresentation S n P g Pm Pi).baseChange y.left).embedding.left := rfl

private theorem groupNative_embedding_left {T : Over S}
    (y : T ⟶ FixedDimension.GroupGlobalParameter.fixedDimensionHilbertGroupParameter S n P g Pm Pi) :
    (Single.ParameterBaseChange.singleParameterBaseChangeIso (GroupUniversalRecovery.fixedDimensionHilbertGroupPointRelativeMap S n P g Pm Pi y)
      (FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily S n P g).family.scheme).inv.left ≫
      ((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n P g).baseChange
        (FixedDimension.GroupPointData.fixedDimensionHilbertGroupPointEquiv S n P g Pm Pi T y).1.left).embedding.left =
      (((FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n P g).baseChange
        (FixedDimension.GroupParameters.fixedDimensionHilbertGroupRelativeParameter S n P g Pm Pi).hom).baseChange
        (GroupUniversalRecovery.fixedDimensionHilbertGroupPointRelativeMap S n P g Pm Pi y).left).embedding.left :=
  Projective.ParameterPullbackCompatibility.ProjectivePullback.parameterPresentationIso_embedding_left
    (FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n P g)
    (GroupUniversalRecovery.fixedDimensionHilbertGroupPointRelativeMap S n P g Pm Pi y)

private theorem groupPointFamilyIso_embedding_left {T : Over S}
    (y : T ⟶ FixedDimension.GroupGlobalParameter.fixedDimensionHilbertGroupParameter S n P g Pm Pi) :
    (GroupUniversalRecovery.fixedDimensionHilbertGroupPointFamilyIso S n P g Pm Pi y).hom.left ≫
      ((FixedDimension.GroupPointData.fixedDimensionHilbertGroupPointEquiv S n P g Pm Pi T y).projective S n P g Pm Pi).embedding.left =
      ((FixedDimension.GroupGlobalParameter.fixedDimensionHilbertGroupUniversalProjectivePresentation S n P g Pm Pi).baseChange y.left).embedding.left :=
  triangle_transfer _ _ _ _ _ _ (groupPointIso_left S n P g Pm Pi y)
    (groupPointEmbedding_left S n P g Pm Pi y) (groupUniversalEmbedding_left S n P g Pm Pi y)
    (groupNative_embedding_left S n P g Pm Pi y)

theorem fixedDimensionHilbertGroupPointFamilyIso_embedding {T : Over S}
    (y : T ⟶ FixedDimension.GroupGlobalParameter.fixedDimensionHilbertGroupParameter S n P g Pm Pi) :
    (GroupUniversalRecovery.fixedDimensionHilbertGroupPointFamilyIso S n P g Pm Pi y).hom ≫
      ((FixedDimension.GroupPointData.fixedDimensionHilbertGroupPointEquiv S n P g Pm Pi T y).projective S n P g Pm Pi).embedding =
      ((FixedDimension.GroupGlobalParameter.fixedDimensionHilbertGroupUniversalProjectivePresentation S n P g Pm Pi).baseChange y.left).embedding := by
  apply Over.OverMorphism.ext
  exact groupPointFamilyIso_embedding_left S n P g Pm Pi y

private theorem abelianPointIso_left {T : Over S}
    (y : T ⟶ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi) :
    (UniversalRecovery.fixedDimensionHilbertAbelianPointFamilyIso S n P g Pm Pi y).hom.left =
      (GroupPullbackComposition.groupPullbackCompIso (FixedDimension.GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi)
        (FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameterInclusion S n P g Pm Pi).left y.left).inv.left ≫
      (GroupUniversalRecovery.fixedDimensionHilbertGroupPointFamilyIso S n P g Pm Pi
        (y ≫ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameterInclusion S n P g Pm Pi)).hom.left := rfl

private theorem abelianPointEmbedding_left {T : Over S}
    (y : T ⟶ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi) :
    ((FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n P g Pm Pi T y).val.projective
      S n P g Pm Pi).embedding.left =
    ((FixedDimension.GroupPointData.fixedDimensionHilbertGroupPointEquiv S n P g Pm Pi T
      (y ≫ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameterInclusion S n P g Pm Pi)).projective
      S n P g Pm Pi).embedding.left := rfl

private theorem abelianUniversalEmbedding_left {T : Over S}
    (y : T ⟶ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi) :
    (((FixedDimension.GroupGlobalParameter.fixedDimensionHilbertGroupUniversalProjectivePresentation S n P g Pm Pi).baseChange
      (FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameterInclusion S n P g Pm Pi).left).baseChange y.left).embedding.left =
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange y.left).embedding.left := rfl

private theorem abelianNative_embedding_left {T : Over S}
    (y : T ⟶ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi) :
    ((GroupPullbackComposition.groupPullbackCompIso (FixedDimension.GroupParameters.fixedDimensionHilbertGroupUniversalFamily S n P g Pm Pi)
      (FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameterInclusion S n P g Pm Pi).left y.left).inv.left ≫
      (GroupUniversalRecovery.fixedDimensionHilbertGroupPointFamilyIso S n P g Pm Pi
        (y ≫ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameterInclusion S n P g Pm Pi)).hom.left) ≫
      ((FixedDimension.GroupPointData.fixedDimensionHilbertGroupPointEquiv S n P g Pm Pi T
        (y ≫ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameterInclusion S n P g Pm Pi)).projective
        S n P g Pm Pi).embedding.left =
      (((FixedDimension.GroupGlobalParameter.fixedDimensionHilbertGroupUniversalProjectivePresentation S n P g Pm Pi).baseChange
        (FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameterInclusion S n P g Pm Pi).left).baseChange y.left).embedding.left :=
  compose_triangles _ _ _ _ _
    (groupPointFamilyIso_embedding_left S n P g Pm Pi
      (y ≫ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameterInclusion S n P g Pm Pi))
    (Projective.ParameterPullbackCompatibility.ProjectivePullback.groupPresentationComposition_embedding_left
      (FixedDimension.GroupGlobalParameter.fixedDimensionHilbertGroupUniversalProjectivePresentation S n P g Pm Pi)
      (FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameterInclusion S n P g Pm Pi).left y.left)

theorem abelianPointFamilyIso_embedding_left {T : Over S}
    (y : T ⟶ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi) :
    (UniversalRecovery.fixedDimensionHilbertAbelianPointFamilyIso S n P g Pm Pi y).hom.left ≫
      ((FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n P g Pm Pi T y).val.projective
        S n P g Pm Pi).embedding.left =
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange y.left).embedding.left :=
  triangle_transfer _ _ _ _ _ _ (abelianPointIso_left S n P g Pm Pi y)
    (abelianPointEmbedding_left S n P g Pm Pi y) (abelianUniversalEmbedding_left S n P g Pm Pi y)
    (abelianNative_embedding_left S n P g Pm Pi y)

theorem fixedDimensionHilbertAbelianPointFamilyIso_embedding {T : Over S}
    (y : T ⟶ FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi) :
    (UniversalRecovery.fixedDimensionHilbertAbelianPointFamilyIso S n P g Pm Pi y).hom ≫
      ((FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n P g Pm Pi T y).val.projective
        S n P g Pm Pi).embedding =
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange y.left).embedding := by
  apply Over.OverMorphism.ext
  exact abelianPointFamilyIso_embedding_left S n P g Pm Pi y

omit [AlgebraicGeometry.IsNoetherian S] in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.PointData.FixedDimensionHilbertAbelianData.eqSchemeIso_embedding {T : Over S}
    {D E : FixedDimension.PointData.FixedDimensionHilbertAbelianData S n P g Pm Pi T} (h : D = E) :
    (Abelian.Schemes.AbelianScheme.eqSchemeIso (congrArg (fun Z => Z.abelianScheme S n P g Pm Pi) h)).hom ≫
      (E.val.projective S n P g Pm Pi).embedding = (D.val.projective S n P g Pm Pi).embedding := by
  apply Over.OverMorphism.ext
  exact abelian_eqSchemeIso_embedding_left
    (fun Z : FixedDimension.PointData.FixedDimensionHilbertAbelianData S n P g Pm Pi T => Z.abelianScheme S n P g Pm Pi)
    (fun Z => (Z.val.projective S n P g Pm Pi).embedding) h

private theorem abelianDataIso_left {T : Over S}
    (D : FixedDimension.PointData.FixedDimensionHilbertAbelianData S n P g Pm Pi T) :
    (DataRecovery.fixedDimensionHilbertAbelianDataFamilyIso S n P g Pm Pi D).hom.left =
      (UniversalRecovery.fixedDimensionHilbertAbelianPointFamilyIso S n P g Pm Pi
        ((FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n P g Pm Pi T).symm D)).hom.left ≫
      (Abelian.Schemes.AbelianScheme.eqSchemeIso (congrArg
        (fun Z : FixedDimension.PointData.FixedDimensionHilbertAbelianData S n P g Pm Pi T => Z.abelianScheme S n P g Pm Pi)
        ((FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n P g Pm Pi T).apply_symm_apply D))).hom.left := rfl

private theorem abelianDataComposite_embedding_left {T : Over S}
    (D : FixedDimension.PointData.FixedDimensionHilbertAbelianData S n P g Pm Pi T) :
    ((UniversalRecovery.fixedDimensionHilbertAbelianPointFamilyIso S n P g Pm Pi
        ((FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n P g Pm Pi T).symm D)).hom.left ≫
      (Abelian.Schemes.AbelianScheme.eqSchemeIso (congrArg
        (fun Z : FixedDimension.PointData.FixedDimensionHilbertAbelianData S n P g Pm Pi T => Z.abelianScheme S n P g Pm Pi)
        ((FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n P g Pm Pi T).apply_symm_apply D))).hom.left) ≫
      (D.val.projective S n P g Pm Pi).embedding.left =
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange
        ((FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n P g Pm Pi T).symm D).left).embedding.left :=
  compose_triangles _ _ _ _ _
    (abelian_eqSchemeIso_embedding_left
      (fun Z : FixedDimension.PointData.FixedDimensionHilbertAbelianData S n P g Pm Pi T => Z.abelianScheme S n P g Pm Pi)
      (fun Z => (Z.val.projective S n P g Pm Pi).embedding)
      ((FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n P g Pm Pi T).apply_symm_apply D))
    (abelianPointFamilyIso_embedding_left S n P g Pm Pi
      ((FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n P g Pm Pi T).symm D))

private theorem abelianDataFamilyIso_embedding_left {T : Over S}
    (D : FixedDimension.PointData.FixedDimensionHilbertAbelianData S n P g Pm Pi T) :
    (DataRecovery.fixedDimensionHilbertAbelianDataFamilyIso S n P g Pm Pi D).hom.left ≫
      (D.val.projective S n P g Pm Pi).embedding.left =
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange
        ((FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n P g Pm Pi T).symm D).left).embedding.left :=
  triangle_of_left_eq _ _ _ _ (abelianDataIso_left S n P g Pm Pi D)
    (abelianDataComposite_embedding_left S n P g Pm Pi D)

theorem fixedDimensionHilbertAbelianDataFamilyIso_embedding {T : Over S}
    (D : FixedDimension.PointData.FixedDimensionHilbertAbelianData S n P g Pm Pi T) :
    (DataRecovery.fixedDimensionHilbertAbelianDataFamilyIso S n P g Pm Pi D).hom ≫
      (D.val.projective S n P g Pm Pi).embedding =
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange
        ((FixedDimension.PointData.fixedDimensionHilbertAbelianNativePointEquiv S n P g Pm Pi T).symm D).left).embedding := by
  apply Over.OverMorphism.ext
  exact abelianDataFamilyIso_embedding_left S n P g Pm Pi D

variable (N : ℕ) [NeZero N]

private theorem fullLevelPointIso_left {T : Over S}
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N) :
    (LevelUniversalRecovery.fixedDimensionHilbertFullLevelPointFamilyIso S n P g Pm Pi N y).hom.left =
      (Single.ParameterBaseChange.singleParameterBaseChangeIso (LevelUniversalRecovery.fixedDimensionHilbertFullLevelPointRelativeMap S n P g Pm Pi N y)
        (FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n P g Pm Pi).scheme).inv.left := rfl

private theorem fullLevelPresentation_embedding :
    Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding
      (FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).embedding
      (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelRelativeParameter S n P g Pm Pi N).hom =
      (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N).embedding :=
  Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding_baseChange (FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi)
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelRelativeParameter S n P g Pm Pi N).hom

private theorem fullLevelUniversalEmbedding_left {T : Over S}
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N) :
    (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding
      (FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).embedding
      (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelRelativeParameter S n P g Pm Pi N).hom) y.left).left =
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N).baseChange y.left).embedding.left :=
  congrArg (fun j => (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding j y.left).left)
    (fullLevelPresentation_embedding S n P g Pm Pi N)

private theorem fullLevelNative_embedding_relative_left {T : Over S}
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N) :
    (Single.ParameterBaseChange.singleParameterBaseChangeIso (LevelUniversalRecovery.fixedDimensionHilbertFullLevelPointRelativeMap S n P g Pm Pi N y)
      (FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n P g Pm Pi).scheme).inv.left ≫
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange
        (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T y).1.left).embedding.left =
      (((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange
        (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelRelativeParameter S n P g Pm Pi N).hom).baseChange
        (LevelUniversalRecovery.fixedDimensionHilbertFullLevelPointRelativeMap S n P g Pm Pi N y).left).embedding.left :=
  Projective.ParameterPullbackCompatibility.ProjectivePullback.parameterPresentationIso_embedding_left
    (FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi)
    (LevelUniversalRecovery.fixedDimensionHilbertFullLevelPointRelativeMap S n P g Pm Pi N y)

private theorem fullLevelRelativePoint_left {T : Over S}
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N) :
    (LevelUniversalRecovery.fixedDimensionHilbertFullLevelPointRelativeMap S n P g Pm Pi N y).left = y.left :=
  CompositeParameterPoints.compositeParameterPointEquiv_relative_left
    (FixedDimension.AbelianParameters.fixedDimensionHilbertAbelianParameter S n P g Pm Pi)
    (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelRelativeParameter S n P g Pm Pi N) T y

private theorem fullLevelRelativeEmbedding_left {T : Over S}
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N) :
    (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding
      (FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).embedding
      (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelRelativeParameter S n P g Pm Pi N).hom)
      (LevelUniversalRecovery.fixedDimensionHilbertFullLevelPointRelativeMap S n P g Pm Pi N y).left).left =
    (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding
      (FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).embedding
      (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelRelativeParameter S n P g Pm Pi N).hom) y.left).left :=
  eq_of_heq (dependent_congr
    (fun h => (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding
      (FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).embedding
      (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelRelativeParameter S n P g Pm Pi N).hom) h).left)
    (fullLevelRelativePoint_left S n P g Pm Pi N y))

private theorem fullLevelNative_embedding_left {T : Over S}
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N) :
    (Single.ParameterBaseChange.singleParameterBaseChangeIso (LevelUniversalRecovery.fixedDimensionHilbertFullLevelPointRelativeMap S n P g Pm Pi N y)
      (FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n P g Pm Pi).scheme).inv.left ≫
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange
        (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T y).1.left).embedding.left =
      (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding (Projective.EmbeddingPullbackComposition.ProjectivePullback.embedding
        (FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).embedding
        (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelRelativeParameter S n P g Pm Pi N).hom) y.left).left :=
  (fullLevelNative_embedding_relative_left S n P g Pm Pi N y).trans
    ((twicePresentationEmbedding_left (FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi)
      (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelRelativeParameter S n P g Pm Pi N).hom
      (LevelUniversalRecovery.fixedDimensionHilbertFullLevelPointRelativeMap S n P g Pm Pi N y).left).trans
      (fullLevelRelativeEmbedding_left S n P g Pm Pi N y))

private theorem fullLevelNativeUniversal_embedding_left {T : Over S}
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N) :
    (Single.ParameterBaseChange.singleParameterBaseChangeIso (LevelUniversalRecovery.fixedDimensionHilbertFullLevelPointRelativeMap S n P g Pm Pi N y)
      (FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianScheme S n P g Pm Pi).scheme).inv.left ≫
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange
        (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T y).1.left).embedding.left =
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N).baseChange y.left).embedding.left :=
  (fullLevelNative_embedding_left S n P g Pm Pi N y).trans
    (fullLevelUniversalEmbedding_left S n P g Pm Pi N y)

theorem fullLevelPointFamilyIso_embedding_left {T : Over S}
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N) :
    (LevelUniversalRecovery.fixedDimensionHilbertFullLevelPointFamilyIso S n P g Pm Pi N y).hom.left ≫
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange
        (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T y).1.left).embedding.left =
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N).baseChange y.left).embedding.left :=
  triangle_of_left_eq _ _ _ _ (fullLevelPointIso_left S n P g Pm Pi N y)
    (fullLevelNativeUniversal_embedding_left S n P g Pm Pi N y)

theorem fixedDimensionHilbertFullLevelPointFamilyIso_embedding {T : Over S}
    (y : T ⟶ FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameter S n P g Pm Pi N) :
    (LevelUniversalRecovery.fixedDimensionHilbertFullLevelPointFamilyIso S n P g Pm Pi N y).hom ≫
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange
        (FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T y).1.left).embedding =
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N).baseChange y.left).embedding := by
  apply Over.OverMorphism.ext
  exact fullLevelPointFamilyIso_embedding_left S n P g Pm Pi N y

omit [NeZero N] in
theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.LevelDataRecovery.FixedDimensionHilbertFullLevelData.eqSchemeIso_embedding {T : Over S}
    {D E : LevelDataRecovery.FixedDimensionHilbertFullLevelData S n P g Pm Pi N T} (h : D = E) :
    (Level.Data.AbelianSchemeWithFullLevel.eqSchemeIso
      (congrArg (fun Z => Z.family S n P g Pm Pi N) h)).hom ≫
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange E.1.left).embedding =
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange D.1.left).embedding := by
  apply Over.OverMorphism.ext
  exact fullLevel_eqSchemeIso_embedding_left
    (fun Z : LevelDataRecovery.FixedDimensionHilbertFullLevelData S n P g Pm Pi N T => Z.family S n P g Pm Pi N)
    (fun Z => ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange Z.1.left).embedding) h

private theorem fullLevelDataIso_left {T : Over S}
    (D : LevelDataRecovery.FixedDimensionHilbertFullLevelData S n P g Pm Pi N T) :
    (LevelDataRecovery.fixedDimensionHilbertFullLevelDataFamilyIso S n P g Pm Pi N D).hom.left =
      (LevelUniversalRecovery.fixedDimensionHilbertFullLevelPointFamilyIso S n P g Pm Pi N
        ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T).symm D)).hom.left ≫
      (Level.Data.AbelianSchemeWithFullLevel.eqSchemeIso (congrArg
        (fun Z : LevelDataRecovery.FixedDimensionHilbertFullLevelData S n P g Pm Pi N T => Z.family S n P g Pm Pi N)
        ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T).apply_symm_apply D))).hom.left := rfl

private theorem fullLevelDataComposite_embedding_left {T : Over S}
    (D : LevelDataRecovery.FixedDimensionHilbertFullLevelData S n P g Pm Pi N T) :
    ((LevelUniversalRecovery.fixedDimensionHilbertFullLevelPointFamilyIso S n P g Pm Pi N
        ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T).symm D)).hom.left ≫
      (Level.Data.AbelianSchemeWithFullLevel.eqSchemeIso (congrArg
        (fun Z : LevelDataRecovery.FixedDimensionHilbertFullLevelData S n P g Pm Pi N T => Z.family S n P g Pm Pi N)
        ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T).apply_symm_apply D))).hom.left) ≫
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange D.1.left).embedding.left =
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N).baseChange
        ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T).symm D).left).embedding.left :=
  compose_triangles _ _ _ _ _
    (fullLevel_eqSchemeIso_embedding_left
      (fun Z : LevelDataRecovery.FixedDimensionHilbertFullLevelData S n P g Pm Pi N T => Z.family S n P g Pm Pi N)
      (fun Z => ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange Z.1.left).embedding)
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T).apply_symm_apply D))
    (fullLevelPointFamilyIso_embedding_left S n P g Pm Pi N
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T).symm D))

private theorem fullLevelDataFamilyIso_embedding_left {T : Over S}
    (D : LevelDataRecovery.FixedDimensionHilbertFullLevelData S n P g Pm Pi N T) :
    (LevelDataRecovery.fixedDimensionHilbertFullLevelDataFamilyIso S n P g Pm Pi N D).hom.left ≫
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange D.1.left).embedding.left =
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N).baseChange
        ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T).symm D).left).embedding.left :=
  triangle_of_left_eq _ _ _ _ (fullLevelDataIso_left S n P g Pm Pi N D)
    (fullLevelDataComposite_embedding_left S n P g Pm Pi N D)

theorem fixedDimensionHilbertFullLevelDataFamilyIso_embedding {T : Over S}
    (D : LevelDataRecovery.FixedDimensionHilbertFullLevelData S n P g Pm Pi N T) :
    (LevelDataRecovery.fixedDimensionHilbertFullLevelDataFamilyIso S n P g Pm Pi N D).hom ≫
      ((FixedDimension.AbelianParameters.fixedDimensionHilbertUniversalAbelianProjectivePresentation S n P g Pm Pi).baseChange D.1.left).embedding =
      ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelUniversalProjectivePresentation S n P g Pm Pi N).baseChange
        ((FixedDimension.LevelParameters.fixedDimensionHilbertFullLevelParameterPointEquiv S n P g Pm Pi N T).symm D).left).embedding := by
  apply Over.OverMorphism.ext
  exact fullLevelDataFamilyIso_embedding_left S n P g Pm Pi N D

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Fixed.DataEmbeddingRecovery
