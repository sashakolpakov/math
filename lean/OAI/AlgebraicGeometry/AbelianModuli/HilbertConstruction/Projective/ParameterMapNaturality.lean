import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ParameterPullbackCompatibility

/-! # Parameter Map Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ParameterMapNaturality.ProjectivePullback

noncomputable section

/-! Naturality of the actual projective embeddings along parameter maps.
The comparison criterion uses the existing closed immersion to identify
morphisms; it does not choose a new presentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

private theorem inverse_triangle {C : Type*} [Category* C]
    {X Y Z : C} (e : X ≅ Y) (i : X ⟶ Z) (j : Y ⟶ Z)
    (h : e.inv ≫ i = j) : e.hom ≫ j = i := by
  rw [← h, e.hom_inv_id_assoc]

private theorem square_of_recovered_triangle {C : Type*} [Category* C]
    {A B D P Q : C} (e : A ≅ B) (f : A ⟶ D) (p : B ⟶ D)
    (j : D ⟶ P) (k : B ⟶ Q) (i : A ⟶ Q) (r : Q ⟶ P)
    (hf : e.hom ≫ p = f) (hk : k ≫ r = p ≫ j) (he : e.hom ≫ k = i) :
    f ≫ j = i ≫ r := by
  rw [← hf, Category.assoc, ← hk, ← Category.assoc, he]

private theorem mappedEqualIndex_embedding {C D I : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (X : I → C) (Y : D) (j : ∀ a, F.obj (X a) ⟶ Y)
    {a b : I} (h : a = b) :
    (F.mapIso (eqToIso (congrArg X h))).hom ≫ j b = j a := by
  subst b
  change F.map (𝟙 (X a)) ≫ j a = j a
  exact (congrArg (fun k => k ≫ j a) (F.map_id (X a))).trans (Category.id_comp _)

theorem parameterMap_embedding {S : Scheme.{u}} {X : Over S} {n : ℕ}
    (j : X ⟶ ProjectivePresentations.projectiveSpaceOver S n) {U T : Over S} (c : U ⟶ T) :
    Single.ParameterBaseChange.singleParameterBaseChangeMap c X ≫ (EmbeddingPullbackComposition.ProjectivePullback.embedding j T.hom).left =
      (EmbeddingPullbackComposition.ProjectivePullback.embedding j U.hom).left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap c.left n := by
  let e := (Over.forget U.left).mapIso (Single.ParameterBaseChange.singleParameterBaseChangeIso c X)
  have he : e.hom ≫ (EmbeddingPullbackComposition.ProjectivePullback.embedding (EmbeddingPullbackComposition.ProjectivePullback.embedding j T.hom) c.left).left =
      (EmbeddingPullbackComposition.ProjectivePullback.embedding j U.hom).left :=
    inverse_triangle e _ _ (ParameterPullbackCompatibility.ProjectivePullback.parameterIso_embedding_left j c)
  exact square_of_recovered_triangle e (Single.ParameterBaseChange.singleParameterBaseChangeMap c X)
    (pullback.fst ((Over.pullback T.hom).obj X).hom c.left)
    (EmbeddingPullbackComposition.ProjectivePullback.embedding j T.hom).left (EmbeddingPullbackComposition.ProjectivePullback.embedding (EmbeddingPullbackComposition.ProjectivePullback.embedding j T.hom) c.left).left
    (EmbeddingPullbackComposition.ProjectivePullback.embedding j U.hom).left (RelativeProjective.BaseMaps.relativeProjectiveBaseMap c.left n)
    (Single.ParameterFunctoriality.singleParameterBaseChangeIso_hom_fst c X)
    (EmbeddingPullbackComposition.ProjectivePullback.embedding_baseMap (EmbeddingPullbackComposition.ProjectivePullback.embedding j T.hom) c.left) he

private theorem equalBase_embedding_left {S T : Scheme.{u}} {X : Over S} {n : ℕ}
    (j : X ⟶ ProjectivePresentations.projectiveSpaceOver S n) {f g : T ⟶ S} (h : f = g) :
    (eqToIso (congrArg (fun a => (Over.pullback a).obj X) h)).hom.left ≫
      (EmbeddingPullbackComposition.ProjectivePullback.embedding j g).left = (EmbeddingPullbackComposition.ProjectivePullback.embedding j f).left :=
  mappedEqualIndex_embedding (Over.forget T) (fun a : T ⟶ S => (Over.pullback a).obj X)
    (ProjectivePresentations.projectiveSpaceOver T n).left (fun a => (EmbeddingPullbackComposition.ProjectivePullback.embedding j a).left) h

theorem equalBase_embedding {S T : Scheme.{u}} {X : Over S} {n : ℕ}
    (j : X ⟶ ProjectivePresentations.projectiveSpaceOver S n) {f g : T ⟶ S} (h : f = g) :
    (eqToIso (congrArg (fun a => (Over.pullback a).obj X) h)).hom ≫
      EmbeddingPullbackComposition.ProjectivePullback.embedding j g = EmbeddingPullbackComposition.ProjectivePullback.embedding j f := by
  apply Over.OverMorphism.ext
  exact equalBase_embedding_left j h

/-- The original projective embeddings determine the naturality of a
comparison between two parameterized families. -/
theorem comparison_natural
    {M N T U : Scheme.{u}} {X : Over M} {Y : Over N} {n : ℕ}
    (j : X ⟶ ProjectivePresentations.projectiveSpaceOver M n) (k : Y ⟶ ProjectivePresentations.projectiveSpaceOver N n)
    {x : T ⟶ M} {y : T ⟶ N} {x' : U ⟶ M} {y' : U ⟶ N}
    (cx : Over.mk x' ⟶ Over.mk x) (cy : Over.mk y' ⟶ Over.mk y)
    (hc : cx.left = cy.left)
    (e : (Over.pullback x).obj X ≅ (Over.pullback y).obj Y)
    (e' : (Over.pullback x').obj X ≅ (Over.pullback y').obj Y)
    (he : e.hom ≫ EmbeddingPullbackComposition.ProjectivePullback.embedding k y = EmbeddingPullbackComposition.ProjectivePullback.embedding j x)
    (he' : e'.hom ≫ EmbeddingPullbackComposition.ProjectivePullback.embedding k y' = EmbeddingPullbackComposition.ProjectivePullback.embedding j x')
    [Mono (EmbeddingPullbackComposition.ProjectivePullback.embedding k y).left] :
    Single.ParameterBaseChange.singleParameterBaseChangeMap cx X ≫ e.hom.left =
      e'.hom.left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap cy Y := by
  apply (cancel_mono (EmbeddingPullbackComposition.ProjectivePullback.embedding k y).left).mp
  have h : e.hom.left ≫ (EmbeddingPullbackComposition.ProjectivePullback.embedding k y).left = (EmbeddingPullbackComposition.ProjectivePullback.embedding j x).left :=
    congrArg Over.Hom.left he
  have h' : e'.hom.left ≫ (EmbeddingPullbackComposition.ProjectivePullback.embedding k y').left = (EmbeddingPullbackComposition.ProjectivePullback.embedding j x').left :=
    congrArg Over.Hom.left he'
  calc
    _ = Single.ParameterBaseChange.singleParameterBaseChangeMap cx X ≫ (EmbeddingPullbackComposition.ProjectivePullback.embedding j x).left := by
      rw [Category.assoc, h]
    _ = (EmbeddingPullbackComposition.ProjectivePullback.embedding j x').left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap cx.left n :=
      parameterMap_embedding j cx
    _ = (EmbeddingPullbackComposition.ProjectivePullback.embedding j x').left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap cy.left n :=
      congrArg (fun q => (EmbeddingPullbackComposition.ProjectivePullback.embedding j x').left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap q n) hc
    _ = e'.hom.left ≫ ((EmbeddingPullbackComposition.ProjectivePullback.embedding k y').left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap cy.left n) :=
      (congrArg (fun q => q ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap cy.left n) h'.symm).trans
        (Category.assoc _ _ _)
    _ = _ := (congrArg (fun q => e'.hom.left ≫ q)
      (parameterMap_embedding k cy).symm).trans (Category.assoc _ _ _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ParameterMapNaturality.ProjectivePullback
