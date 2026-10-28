import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SliceCharacters
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterFunctor

/-! # Character Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality

noncomputable section

/-!
# CartierDuality: restriction of character sheaves to a base change
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj
open scoped _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u v w z

namespace CharacterBaseChange.Construction.Slices

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]

/-- On a slice site, a natural morphism over a test object is unchanged
by replacing the iterated slice with its equivalent ordinary slice. -/
def presheafHomOverEquiv (T : C) (F G : Cᵒᵖ ⥤ D) (U : Over T) :
    (presheafHom F G).obj (Opposite.op U.left) ≃
      (presheafHom ((Over.forget T).op ⋙ F) ((Over.forget T).op ⋙ G)).obj
        (Opposite.op U) :=
  (Equivalence.congrLeft U.iteratedSliceEquiv.op).fullyFaithfulInverse.homEquiv

/-- Restriction of internal Hom to a slice agrees with the internal Hom
of the two restricted presheaves. -/
def presheafHomOverIso (T : C) (F G : Cᵒᵖ ⥤ D) :
    (Over.forget T).op ⋙ presheafHom F G ≅
      presheafHom ((Over.forget T).op ⋙ F) ((Over.forget T).op ⋙ G) :=
  NatIso.ofComponents (fun U => (presheafHomOverEquiv T F G U.unop).toIso) (by
    intro U V f
    ext χ
    apply NatTrans.ext
    rfl)

/-- Isomorphisms of source and target presheaves induce an isomorphism
of their internal Hom presheaves. -/
def presheafHomCongr {F₁ F₂ G₁ G₂ : Cᵒᵖ ⥤ D} (e : F₁ ≅ F₂) (d : G₁ ≅ G₂) :
    presheafHom F₁ G₁ ≅ presheafHom F₂ G₂ :=
  NatIso.ofComponents (fun T =>
    (((Functor.isoWhiskerLeft (Over.forget T.unop).op e).homFromEquiv).trans
      ((Functor.isoWhiskerLeft (Over.forget T.unop).op d).homToEquiv)).toIso) (by
    intro U V f
    ext χ
    apply NatTrans.ext
    rfl)

variable {C' : Type u} [Category.{v} C']

/-- A functor induces the canonical restriction comparison for internal
Hom by precomposition on every slice category. -/
def presheafHomWhiskerMap (H : C' ⥤ C) (F G : Cᵒᵖ ⥤ D) :
    H.op ⋙ presheafHom F G ⟶ presheafHom (H.op ⋙ F) (H.op ⋙ G) where
  app T := ↾(Functor.whiskerLeft (Over.post (X := T.unop) H).op)
  naturality := by
    intro U V f
    ext χ
    apply NatTrans.ext
    funext W
    change χ.app (Opposite.op (Over.mk (H.map W.unop.hom ≫ H.map f.unop))) =
      χ.app (Opposite.op (Over.mk (H.map (W.unop.hom ≫ f.unop))))
    exact presheafHom_map_app (H.map W.unop.hom) (H.map f.unop)
      (H.map (W.unop.hom ≫ f.unop)) (H.map_comp W.unop.hom f.unop).symm χ

/-- If a functor gives an equivalence on every slice, internal Hom
commutes with restriction along that functor. -/
theorem presheafHomWhiskerMap_isIso (H : C' ⥤ C) (F G : Cᵒᵖ ⥤ D)
    [∀ X : C', (Over.post (X := X) H).IsEquivalence] :
    IsIso (presheafHomWhiskerMap H F G) := by
  have (T : C'ᵒᵖ) : IsIso ((presheafHomWhiskerMap H F G).app T) := by
    apply (CategoryTheory.isIso_iff_bijective _).mpr
    exact (Equivalence.congrLeft
      ((Over.post (X := T.unop) H).asEquivalence.op)).fullyFaithfulInverse.homEquiv.bijective
  exact NatIso.isIso_of_isIso_app _

/-- Composition with a base morphism induces an equivalence on each
further slice, since both iterated slices are schemes over the same object. -/
def overPostMapIso {S T : C} (f : T ⟶ S) (U : Over T) :
    U.iteratedSliceForward ⋙ ((Over.map f).obj U).iteratedSliceBackward ≅
      Over.post (X := U) (Over.map f) :=
  NatIso.ofComponents (fun W =>
    Over.isoMk (Over.isoMk (Iso.refl W.left.left) (by
      change 𝟙 _ ≫ (W.left.hom ≫ f) = W.hom.left ≫ U.hom ≫ f
      exact (Category.id_comp _).trans
        ((congrArg (fun k => k ≫ f) W.hom.w).symm.trans
          (Category.assoc W.hom.left U.hom f)))) (by
      apply Over.OverMorphism.ext
      exact Category.id_comp _)) (by
    intro V W k
    apply Over.OverMorphism.ext
    apply Over.OverMorphism.ext
    exact (Category.comp_id k.left.left).trans (Category.id_comp k.left.left).symm)

instance overPostMapIsEquivalence {S T : C} (f : T ⟶ S) (U : Over T) :
    (Over.post (X := U) (Over.map f)).IsEquivalence := by
  let : U.iteratedSliceForward.IsEquivalence :=
    inferInstanceAs U.iteratedSliceEquiv.functor.IsEquivalence
  let : ((Over.map f).obj U).iteratedSliceBackward.IsEquivalence :=
    inferInstanceAs ((Over.map f).obj U).iteratedSliceEquiv.inverse.IsEquivalence
  exact Functor.isEquivalence_of_iso (overPostMapIso f U)

variable [CartesianMonoidalCategory C] [HasPullbacks C]

/-- Characters restrict to the characters of the native pullback group
objects in the slice, compatibly on all further test objects. -/
def starCharacterPresheafIso (T : C) (G K : Grp C) :
    (Over.forget T).op ⋙ presheafHom (yonedaGrp.obj G) (yonedaGrp.obj K) ≅
      presheafHom (yonedaGrp.obj ((Over.star T).mapGrp.obj G))
        (yonedaGrp.obj ((Over.star T).mapGrp.obj K)) :=
  presheafHomOverIso T (yonedaGrp.obj G) (yonedaGrp.obj K) ≪≫
    presheafHomCongr (SliceCharacters.Construction.Slices.starGroupPointIso T G) (SliceCharacters.Construction.Slices.starGroupPointIso T K)

end CharacterBaseChange.Construction.Slices

/-- The ordinary pullback adjunction preserves the group law on points. -/
def CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv {S T : Scheme.{u}} (f : T ⟶ S)
    (G : Grp (Over S)) (U : Over T) :
    ((Over.map f).obj U ⟶ G.X) ≃* (U ⟶ (Over.pullback f).obj G.X) where
  toEquiv := (Over.mapPullbackAdj f).homEquiv U G.X
  map_mul' x y := by
    change (Over.mapPullbackAdj f).unit.app U ≫ (Over.pullback f).map (x * y) =
      ((Over.mapPullbackAdj f).unit.app U ≫ (Over.pullback f).map x) *
        ((Over.mapPullbackAdj f).unit.app U ≫ (Over.pullback f).map y)
    rw [Functor.map_mul, MonObj.comp_mul]

/-- Restricting the functor of group-valued points along a base change
gives the points of the native pullback group scheme. -/
def CharacterBaseChange.Construction.Schemes.pullbackGroupPointIso {S T : Scheme.{u}} (f : T ⟶ S) (G : Grp (Over S)) :
    (Over.map f).op ⋙ yonedaGrp.obj G ≅
      yonedaGrp.obj ((Over.pullback f).mapGrp.obj G) :=
  NatIso.ofComponents (fun U => (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f G U.unop).toGrpIso) (by
    intro U V g
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact (Over.mapPullbackAdj f).homEquiv_naturality_left g.unop x)

/-- Formation of the actual character presheaf commutes with arbitrary
scheme base change, including nonflat base changes. -/
def CharacterBaseChange.Construction.Schemes.characterBaseChangePresheafIso {S T : Scheme.{u}} (f : T ⟶ S) (G : Grp (Over S)) :
    (Over.map f).op ⋙ (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj ≅
      (CharacterSheaf.Construction.Schemes.characterSheaf T ((Over.pullback f).mapGrp.obj G)).obj := by
  let c := CharacterBaseChange.Construction.Slices.presheafHomWhiskerMap (Over.map f)
    (yonedaGrp.obj G) (yonedaGrp.obj (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S))
  let hc : IsIso c := CharacterBaseChange.Construction.Slices.presheafHomWhiskerMap_isIso (Over.map f)
    (yonedaGrp.obj G) (yonedaGrp.obj (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S))
  let e := @asIso _ _ _ _ c hc
  exact e ≪≫ CharacterBaseChange.Construction.Slices.presheafHomCongr (CharacterBaseChange.Construction.Schemes.pullbackGroupPointIso f G)
    (CharacterBaseChange.Construction.Schemes.pullbackGroupPointIso f (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) ≪≫
      yonedaGrp.mapIso (SliceCharacters.Construction.Schemes.multiplicativeGroup_pullbackIso f))

/-- The character-sheaf comparison for an arbitrary base morphism is
an isomorphism of the actual fppf sheaves. -/
def CharacterBaseChange.Construction.Schemes.characterBaseChangeIso {S T : Scheme.{u}} (f : T ⟶ S) (G : Grp (Over S)) :
    (Scheme.fppfTopology.overMapPullback (Type (u + 1)) f).obj (CharacterSheaf.Construction.Schemes.characterSheaf S G) ≅
      CharacterSheaf.Construction.Schemes.characterSheaf T ((Over.pullback f).mapGrp.obj G) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (CharacterBaseChange.Construction.Schemes.characterBaseChangePresheafIso f G)

/-- Restriction of a represented point presheaf is represented by the
scheme-theoretic pullback. -/
def CharacterBaseChange.Construction.Schemes.pointBaseChangePresheafIso {S T : Scheme.{u}} (f : T ⟶ S) (X : Over S) :
    (Over.map f).op ⋙ uliftYoneda.{u + 1}.obj X ≅
      uliftYoneda.{u + 1}.obj ((Over.pullback f).obj X) :=
  NatIso.ofComponents (fun U =>
    (Equiv.ulift.trans (((Over.mapPullbackAdj f).homEquiv U.unop X).trans
      Equiv.ulift.symm)).toIso) (by
    intro U V g
    ext x
    apply ULift.ext
    exact (Over.mapPullbackAdj f).homEquiv_naturality_left g.unop x.down)

/-- Pulling back a represented fppf sheaf gives the sheaf represented
by the native pullback scheme. -/
def CharacterBaseChange.Construction.Schemes.pointBaseChangeIso {S T : Scheme.{u}} (f : T ⟶ S) (X : Over S) :
    (Scheme.fppfTopology.overMapPullback (Type (u + 1)) f).obj (CharacterFunctor.Construction.Schemes.pointSheaf S X) ≅
      CharacterFunctor.Construction.Schemes.pointSheaf T ((Over.pullback f).obj X) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (CharacterBaseChange.Construction.Schemes.pointBaseChangePresheafIso f X)

/-- Finite locally free representability is invariant under sheaf isomorphism. -/
theorem CharacterFunctor.Construction.Schemes.FiniteLocallyFreeRepresentable.of_iso {S : Scheme.{u}}
    {F G : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))}
    (h : CharacterFunctor.Construction.Schemes.FiniteLocallyFreeRepresentable F) (e : F ≅ G) :
    CharacterFunctor.Construction.Schemes.FiniteLocallyFreeRepresentable G := by
  obtain ⟨X, hf, hflat, hfp, ⟨i⟩⟩ := h
  exact ⟨X, hf, hflat, hfp, ⟨i ≪≫ e⟩⟩

/-- Finite locally free representability survives every scheme base change. -/
theorem CharacterFunctor.Construction.Schemes.FiniteLocallyFreeRepresentable.baseChange {S T : Scheme.{u}} (f : T ⟶ S)
    {F : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))}
    (h : CharacterFunctor.Construction.Schemes.FiniteLocallyFreeRepresentable F) :
    CharacterFunctor.Construction.Schemes.FiniteLocallyFreeRepresentable
      ((Scheme.fppfTopology.overMapPullback (Type (u + 1)) f).obj F) := by
  obtain ⟨X, hf, hflat, hfp, ⟨i⟩⟩ := h
  let : IsFinite X.hom := hf
  let : Flat X.hom := hflat
  let : LocallyOfFinitePresentation X.hom := hfp
  refine ⟨(Over.pullback f).obj X, ?_, ?_, ?_, ?_⟩
  · change IsFinite (Limits.pullback.snd X.hom f)
    infer_instance
  · change Flat (Limits.pullback.snd X.hom f)
    infer_instance
  · change LocallyOfFinitePresentation (Limits.pullback.snd X.hom f)
    infer_instance
  · exact ⟨(CharacterBaseChange.Construction.Schemes.pointBaseChangeIso f X).symm ≪≫
      (Scheme.fppfTopology.overMapPullback (Type (u + 1)) f).mapIso i⟩

/-- A finite locally free representative of a character sheaf pulls
back to a representative of the characters of the base-changed group. -/
theorem CharacterBaseChange.Construction.Schemes.characterRepresentability_baseChange {S T : Scheme.{u}} (f : T ⟶ S)
    (G : Grp (Over S)) (h : CharacterFunctor.Construction.Schemes.FiniteLocallyFreeRepresentable (CharacterSheaf.Construction.Schemes.characterSheaf S G)) :
    CharacterFunctor.Construction.Schemes.FiniteLocallyFreeRepresentable (CharacterSheaf.Construction.Schemes.characterSheaf T ((Over.pullback f).mapGrp.obj G)) :=
  (h.baseChange f).of_iso (CharacterBaseChange.Construction.Schemes.characterBaseChangeIso f G)

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality
