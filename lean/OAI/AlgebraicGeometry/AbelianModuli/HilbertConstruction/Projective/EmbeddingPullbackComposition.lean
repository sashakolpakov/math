import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.BaseChangeIsoProjections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.BaseFunctoriality

/-! # Embedding Pullback Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.EmbeddingPullbackComposition.ProjectivePullback

noncomputable section

/-! Native projective pullback embeddings commute with composition.
The comparison is proved from their actual projections to projective
space and does not choose a new presentation or a new family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable {S T U : Scheme.{u}} {n : ℕ} {X Y : Over S}

private theorem map_comp_postcomp
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X Y Z : C} {W : D} (a : X ⟶ Y) (b : Y ⟶ Z) (c : F.obj Z ⟶ W) :
    F.map a ≫ (F.map b ≫ c) = F.map (a ≫ b) ≫ c :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (fun h => h ≫ c) (F.map_comp a b).symm)

private theorem comp_eq_of_factor_eq
    {C : Type*} [Category* C] {X Y Z : C}
    (a : X ⟶ Y) (b c : Y ⟶ Z) (d : X ⟶ Z)
    (hbc : b = c) (hab : a ≫ b = d) : a ≫ c = d :=
  (congrArg (fun h => a ≫ h) hbc.symm).trans hab

private theorem composite_projection
    {C : Type*} [Category* C] {A B E N P Q R : C}
    (e : N ⟶ E) (a : N ⟶ B) (b : B ⟶ A) (c : E ⟶ A)
    (j : A ⟶ P) (i : B ⟶ Q) (k : N ⟶ R) (l : E ⟶ R)
    (r : Q ⟶ P) (s : R ⟶ Q) (t : R ⟶ P)
    (he : e ≫ c = a ≫ b) (hi : i ≫ r = b ≫ j)
    (hk : k ≫ s = a ≫ i) (hl : l ≫ t = c ≫ j) (ht : t = s ≫ r) :
    (e ≫ l) ≫ t = k ≫ t := by
  calc
    (e ≫ l) ≫ t = e ≫ (l ≫ t) := Category.assoc _ _ _
    _ = e ≫ (c ≫ j) := congrArg (fun h => e ≫ h) hl
    _ = (e ≫ c) ≫ j := (Category.assoc _ _ _).symm
    _ = (a ≫ b) ≫ j := congrArg (fun h => h ≫ j) he
    _ = a ≫ (b ≫ j) := Category.assoc _ _ _
    _ = a ≫ (i ≫ r) := congrArg (fun h => a ≫ h) hi.symm
    _ = (a ≫ i) ≫ r := (Category.assoc _ _ _).symm
    _ = (k ≫ s) ≫ r := congrArg (fun h => h ≫ r) hk.symm
    _ = k ≫ (s ≫ r) := Category.assoc _ _ _
    _ = k ≫ t := congrArg (fun h => k ≫ h) ht.symm

/-- The morphism used by the existing projective-presentation pullback. -/
def embedding (j : X ⟶ ProjectivePresentations.projectiveSpaceOver S n) (f : T ⟶ S) :
    (Over.pullback f).obj X ⟶ ProjectivePresentations.projectiveSpaceOver T n :=
  (Over.pullback f).map j ≫ (SpaceBaseChange.projectiveSpaceOverBaseChangeIso f n).inv

theorem embedding_baseChange (P : ProjectivePresentations.ProjectivePresentation X) (f : T ⟶ S) :
    ProjectivePullback.embedding P.embedding f = (P.baseChange f).embedding := rfl

private theorem baseChange_comp_left_eq (P : ProjectivePresentations.ProjectivePresentation X) (f : T ⟶ S)
    {Z : Over T} (a : Z ⟶ (Over.pullback f).obj X)
    (i : Z ⟶ ProjectivePresentations.projectiveSpaceOver T P.dimension)
    (h : a ≫ ProjectivePullback.embedding P.embedding f = i) :
    a.left ≫ (P.baseChange f).embedding.left = i.left :=
  comp_eq_of_factor_eq a.left (ProjectivePullback.embedding P.embedding f).left (P.baseChange f).embedding.left i.left
    (congrArg Over.Hom.left (embedding_baseChange P f)) (congrArg Over.Hom.left h)

theorem baseChange_comp_eq (P : ProjectivePresentations.ProjectivePresentation X) (f : T ⟶ S)
    {Z : Over T} (a : Z ⟶ (Over.pullback f).obj X)
    (i : Z ⟶ ProjectivePresentations.projectiveSpaceOver T P.dimension)
    (h : a ≫ ProjectivePullback.embedding P.embedding f = i) :
    a ≫ (show (Over.pullback f).obj X ⟶ ProjectivePresentations.projectiveSpaceOver T P.dimension from
      (P.baseChange f).embedding) = i := by
  apply Over.OverMorphism.ext
  exact baseChange_comp_left_eq P f a i h

private theorem embedding_comp_left_eq (P : ProjectivePresentations.ProjectivePresentation X) (f : T ⟶ S)
    {Z : Over T} (a : Z ⟶ (Over.pullback f).obj X)
    (i : Z ⟶ ProjectivePresentations.projectiveSpaceOver T P.dimension)
    (h : a ≫ (P.baseChange f).embedding = i) :
    a.left ≫ (ProjectivePullback.embedding P.embedding f).left = i.left :=
  comp_eq_of_factor_eq a.left (P.baseChange f).embedding.left (ProjectivePullback.embedding P.embedding f).left i.left
    (congrArg Over.Hom.left (embedding_baseChange P f).symm) (congrArg Over.Hom.left h)

theorem embedding_comp_eq (P : ProjectivePresentations.ProjectivePresentation X) (f : T ⟶ S)
    {Z : Over T} (a : Z ⟶ (Over.pullback f).obj X)
    (i : Z ⟶ ProjectivePresentations.projectiveSpaceOver T P.dimension)
    (h : a ≫ (P.baseChange f).embedding = i) :
    a ≫ ProjectivePullback.embedding P.embedding f = i := by
  apply Over.OverMorphism.ext
  exact embedding_comp_left_eq P f a i h

theorem embedding_baseMap (j : X ⟶ ProjectivePresentations.projectiveSpaceOver S n) (f : T ⟶ S) :
    (ProjectivePullback.embedding j f).left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n =
      pullback.fst X.hom f ≫ j.left := by
  change (((Over.pullback f).map j).left ≫
    (SpaceBaseChange.projectiveSpaceOverBaseChangeIso f n).inv.left) ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => ((Over.pullback f).map j).left ≫ a)
      (BaseChangeIsoProjections.projectiveSpaceOverBaseChangeIso_inv_baseMap f n)).trans
      (Pullback.Comparisons.overPullback_map_left_fst j f))

private theorem embedding_precomp_left
    (a : Y ⟶ X) (j : X ⟶ ProjectivePresentations.projectiveSpaceOver S n) (f : T ⟶ S) :
    ((Over.pullback f).map a).left ≫ (ProjectivePullback.embedding j f).left =
      (ProjectivePullback.embedding (a ≫ j) f).left :=
  map_comp_postcomp ((Over.pullback f) ⋙ Over.forget T) a j
    (SpaceBaseChange.projectiveSpaceOverBaseChangeIso f n).inv.left

theorem embedding_precomp (a : Y ⟶ X) (j : X ⟶ ProjectivePresentations.projectiveSpaceOver S n) (f : T ⟶ S) :
    (Over.pullback f).map a ≫ ProjectivePullback.embedding j f = ProjectivePullback.embedding (a ≫ j) f := by
  apply Over.OverMorphism.ext
  exact embedding_precomp_left a j f

private theorem overHom_eq_of_pullback_projection
    {S T : Scheme.{u}} {P : Over S} {Q X : Over T}
    (f : T ⟶ S) (p : Q.left ⟶ P.left) (hp : IsPullback p Q.hom P.hom f)
    (a b : X ⟶ Q) (h : a.left ≫ p = b.left ≫ p) : a = b := by
  apply Over.OverMorphism.ext
  exact hp.hom_ext h (a.w.trans b.w.symm)

private theorem embedding_comp_projection
    (j : X ⟶ ProjectivePresentations.projectiveSpaceOver S n) (f : T ⟶ S) (g : U ⟶ T) :
    (((Over.pullbackComp g f).inv.app X).left ≫ (ProjectivePullback.embedding j (g ≫ f)).left) ≫
        RelativeProjective.BaseMaps.relativeProjectiveBaseMap (g ≫ f) n =
      (ProjectivePullback.embedding (ProjectivePullback.embedding j f) g).left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap (g ≫ f) n :=
  composite_projection ((Over.pullbackComp g f).inv.app X).left
    (pullback.fst ((Over.pullback f).obj X).hom g) (pullback.fst X.hom f)
    (pullback.fst X.hom (g ≫ f)) j.left (ProjectivePullback.embedding j f).left
    (ProjectivePullback.embedding (ProjectivePullback.embedding j f) g).left (ProjectivePullback.embedding j (g ≫ f)).left
    (RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n) (RelativeProjective.BaseMaps.relativeProjectiveBaseMap g n)
    (RelativeProjective.BaseMaps.relativeProjectiveBaseMap (g ≫ f) n) (BaseChangeIsoProjections.pullbackComp_inv_fst X f g)
    (embedding_baseMap j f) (embedding_baseMap (ProjectivePullback.embedding j f) g)
    (embedding_baseMap j (g ≫ f)) (RelativeProjective.BaseFunctoriality.relativeProjectiveBaseMap_comp f g n)

theorem embedding_comp (j : X ⟶ ProjectivePresentations.projectiveSpaceOver S n) (f : T ⟶ S) (g : U ⟶ T) :
    (Over.pullbackComp g f).inv.app X ≫ ProjectivePullback.embedding j (g ≫ f) =
      ProjectivePullback.embedding (ProjectivePullback.embedding j f) g :=
  overHom_eq_of_pullback_projection (g ≫ f) (RelativeProjective.BaseMaps.relativeProjectiveBaseMap (g ≫ f) n)
    (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback (g ≫ f) n)
    ((Over.pullbackComp g f).inv.app X ≫ ProjectivePullback.embedding j (g ≫ f))
    (ProjectivePullback.embedding (ProjectivePullback.embedding j f) g) (embedding_comp_projection j f g)

/-- Restrict an existing native-family comparison along an arbitrary base map. -/
def recoveryIso {Y : Over T} (f : T ⟶ S)
    (e : Y ≅ (Over.pullback f).obj X) (g : U ⟶ T) :
    (Over.pullback g).obj Y ≅ (Over.pullback (g ≫ f)).obj X :=
  (Over.pullback g).mapIso e ≪≫ (Over.pullbackComp g f).symm.app X

private theorem recoveryIso_embedding_left {Y : Over T}
    (j : X ⟶ ProjectivePresentations.projectiveSpaceOver S n) (f : T ⟶ S)
    (i : Y ⟶ ProjectivePresentations.projectiveSpaceOver T n) (e : Y ≅ (Over.pullback f).obj X)
    (he : e.hom ≫ ProjectivePullback.embedding j f = i) (g : U ⟶ T) :
    (recoveryIso f e g).hom.left ≫ (ProjectivePullback.embedding j (g ≫ f)).left = (ProjectivePullback.embedding i g).left := by
  change (((Over.pullback g).map e.hom).left ≫ ((Over.pullbackComp g f).inv.app X).left) ≫
    (ProjectivePullback.embedding j (g ≫ f)).left = (ProjectivePullback.embedding i g).left
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun h => ((Over.pullback g).map e.hom).left ≫ h)
      (congrArg Over.Hom.left (embedding_comp j f g))).trans
      ((embedding_precomp_left e.hom (ProjectivePullback.embedding j f) g).trans
        (congrArg (fun h => (ProjectivePullback.embedding h g).left) he)))

theorem recoveryIso_embedding {Y : Over T}
    (j : X ⟶ ProjectivePresentations.projectiveSpaceOver S n) (f : T ⟶ S)
    (i : Y ⟶ ProjectivePresentations.projectiveSpaceOver T n) (e : Y ≅ (Over.pullback f).obj X)
    (he : e.hom ≫ ProjectivePullback.embedding j f = i) (g : U ⟶ T) :
    (recoveryIso f e g).hom ≫ ProjectivePullback.embedding j (g ≫ f) = ProjectivePullback.embedding i g := by
  apply Over.OverMorphism.ext
  exact recoveryIso_embedding_left j f i e he g

theorem recoveryIso_embedding_eq {Y : Over T}
    (j : X ⟶ ProjectivePresentations.projectiveSpaceOver S n) (f : T ⟶ S)
    (i : Y ⟶ ProjectivePresentations.projectiveSpaceOver T n) (e : Y ≅ (Over.pullback f).obj X)
    (he : e.hom ≫ ProjectivePullback.embedding j f = i) (g : U ⟶ T)
    (k : (Over.pullback g).obj Y ⟶ ProjectivePresentations.projectiveSpaceOver U n)
    (hk : ProjectivePullback.embedding i g = k) :
    (recoveryIso f e g).hom ≫ ProjectivePullback.embedding j (g ≫ f) = k :=
  (recoveryIso_embedding j f i e he g).trans hk

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.EmbeddingPullbackComposition.ProjectivePullback
