import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.EmbeddingPullbackComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterLevelPointComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ParameterPullbackCoherence

/-! # Parameter Pullback Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ParameterPullbackCompatibility.ProjectivePullback

noncomputable section

/-! The actual parameter-pullback comparisons preserve the existing
projective embeddings. No new projective presentation is chosen. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}} {X : Over S} {n : ℕ}

theorem parameterIso_embedding_left
    (j : X ⟶ ProjectivePresentations.projectiveSpaceOver S n) {U T : Over S} (c : U ⟶ T) :
    (Single.ParameterBaseChange.singleParameterBaseChangeIso c X).inv.left ≫ (EmbeddingPullbackComposition.ProjectivePullback.embedding j U.hom).left =
      (EmbeddingPullbackComposition.ProjectivePullback.embedding (EmbeddingPullbackComposition.ProjectivePullback.embedding j T.hom) c.left).left := by
  let e := (Single.ParameterBaseChange.singleParameterBaseChangeIso c X).inv
  let i := EmbeddingPullbackComposition.ProjectivePullback.embedding j U.hom
  let k := EmbeddingPullbackComposition.ProjectivePullback.embedding (EmbeddingPullbackComposition.ProjectivePullback.embedding j T.hom) c.left
  let r := RelativeProjective.BaseMaps.relativeProjectiveBaseMap U.hom n
  have hr : r = RelativeProjective.BaseMaps.relativeProjectiveBaseMap c.left n ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap T.hom n :=
    (congrArg (fun b => RelativeProjective.BaseMaps.relativeProjectiveBaseMap b n) c.w.symm).trans
      (RelativeProjective.BaseFunctoriality.relativeProjectiveBaseMap_comp T.hom c.left n)
  have hi : i.left ≫ r = pullback.fst X.hom U.hom ≫ j.left := EmbeddingPullbackComposition.ProjectivePullback.embedding_baseMap j U.hom
  have hk : k.left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap c.left n =
      pullback.fst ((Over.pullback T.hom).obj X).hom c.left ≫ (EmbeddingPullbackComposition.ProjectivePullback.embedding j T.hom).left :=
    EmbeddingPullbackComposition.ProjectivePullback.embedding_baseMap (EmbeddingPullbackComposition.ProjectivePullback.embedding j T.hom) c.left
  have he : e.left ≫ pullback.fst X.hom U.hom =
      pullback.fst ((Over.pullback T.hom).obj X).hom c.left ≫ pullback.fst X.hom T.hom :=
    ParameterLevelPointComparison.singleParameterBaseChangeIso_inv_original_fst c X
  apply (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback U.hom n).hom_ext
  · change (e.left ≫ i.left) ≫ r = k.left ≫ r
    calc
      (e.left ≫ i.left) ≫ r = e.left ≫ (i.left ≫ r) := Category.assoc _ _ _
      _ = e.left ≫ (pullback.fst X.hom U.hom ≫ j.left) := congrArg (fun z => e.left ≫ z) hi
      _ = (e.left ≫ pullback.fst X.hom U.hom) ≫ j.left := (Category.assoc _ _ _).symm
      _ = (pullback.fst ((Over.pullback T.hom).obj X).hom c.left ≫
          pullback.fst X.hom T.hom) ≫ j.left := congrArg (fun z => z ≫ j.left) he
      _ = pullback.fst ((Over.pullback T.hom).obj X).hom c.left ≫
          ((EmbeddingPullbackComposition.ProjectivePullback.embedding j T.hom).left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap T.hom n) := by
        rw [EmbeddingPullbackComposition.ProjectivePullback.embedding_baseMap, Category.assoc]
      _ = (pullback.fst ((Over.pullback T.hom).obj X).hom c.left ≫
          (EmbeddingPullbackComposition.ProjectivePullback.embedding j T.hom).left) ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap T.hom n :=
        (Category.assoc _ _ _).symm
      _ = (k.left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap c.left n) ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap T.hom n :=
        congrArg (fun z => z ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap T.hom n) hk.symm
      _ = k.left ≫ (RelativeProjective.BaseMaps.relativeProjectiveBaseMap c.left n ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap T.hom n) :=
        Category.assoc _ _ _
      _ = k.left ≫ r := congrArg (fun z => k.left ≫ z) hr.symm
  · exact (e ≫ i).w.trans k.w.symm

theorem parameterIso_embedding
    (j : X ⟶ ProjectivePresentations.projectiveSpaceOver S n) {U T : Over S} (c : U ⟶ T) :
    (Single.ParameterBaseChange.singleParameterBaseChangeIso c X).inv ≫ EmbeddingPullbackComposition.ProjectivePullback.embedding j U.hom =
      EmbeddingPullbackComposition.ProjectivePullback.embedding (EmbeddingPullbackComposition.ProjectivePullback.embedding j T.hom) c.left := by
  apply Over.OverMorphism.ext
  exact parameterIso_embedding_left j c

theorem parameterPresentationIso_embedding_left
    (P : ProjectivePresentations.ProjectivePresentation X) {U T : Over S} (c : U ⟶ T) :
    (Single.ParameterBaseChange.singleParameterBaseChangeIso c X).inv.left ≫ (P.baseChange U.hom).embedding.left =
      ((P.baseChange T.hom).baseChange c.left).embedding.left :=
  parameterIso_embedding_left P.embedding c

theorem parameterPresentationIso_embedding
    (P : ProjectivePresentations.ProjectivePresentation X) {U T : Over S} (c : U ⟶ T) :
    (Single.ParameterBaseChange.singleParameterBaseChangeIso c X).inv ≫ (P.baseChange U.hom).embedding =
      ((P.baseChange T.hom).baseChange c.left).embedding := by
  apply Over.OverMorphism.ext
  exact parameterIso_embedding_left P.embedding c

private theorem groupPullbackCompIso_eq [GrpObj X] {T U : Scheme.{u}}
    (f : T ⟶ S) (h : U ⟶ T) :
    GroupPullbackComposition.groupPullbackCompIso X f h = (Over.pullbackComp h f).app X := by
  apply Iso.ext
  exact LineBundle.ParameterPullbackCoherence.groupPullbackCompIso_hom_eq X f h

theorem groupComposition_embedding_left [GrpObj X] {T U : Scheme.{u}}
    (j : X ⟶ ProjectivePresentations.projectiveSpaceOver S n) (f : T ⟶ S) (h : U ⟶ T) :
    (GroupPullbackComposition.groupPullbackCompIso X f h).inv.left ≫ (EmbeddingPullbackComposition.ProjectivePullback.embedding j (h ≫ f)).left =
      (EmbeddingPullbackComposition.ProjectivePullback.embedding (EmbeddingPullbackComposition.ProjectivePullback.embedding j f) h).left := by
  have he := congrArg Over.Hom.left (congrArg Iso.inv (groupPullbackCompIso_eq (X := X) f h))
  exact (congrArg (fun a => a ≫ (EmbeddingPullbackComposition.ProjectivePullback.embedding j (h ≫ f)).left) he).trans
    (congrArg Over.Hom.left (EmbeddingPullbackComposition.ProjectivePullback.embedding_comp j f h))

theorem groupComposition_embedding [GrpObj X] {T U : Scheme.{u}}
    (j : X ⟶ ProjectivePresentations.projectiveSpaceOver S n) (f : T ⟶ S) (h : U ⟶ T) :
    (GroupPullbackComposition.groupPullbackCompIso X f h).inv ≫ EmbeddingPullbackComposition.ProjectivePullback.embedding j (h ≫ f) =
      EmbeddingPullbackComposition.ProjectivePullback.embedding (EmbeddingPullbackComposition.ProjectivePullback.embedding j f) h := by
  apply Over.OverMorphism.ext
  exact groupComposition_embedding_left j f h

theorem groupPresentationComposition_embedding_left [GrpObj X] {T U : Scheme.{u}}
    (P : ProjectivePresentations.ProjectivePresentation X) (f : T ⟶ S) (h : U ⟶ T) :
    (GroupPullbackComposition.groupPullbackCompIso X f h).inv.left ≫ (P.baseChange (h ≫ f)).embedding.left =
      ((P.baseChange f).baseChange h).embedding.left :=
  groupComposition_embedding_left P.embedding f h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ParameterPullbackCompatibility.ProjectivePullback
