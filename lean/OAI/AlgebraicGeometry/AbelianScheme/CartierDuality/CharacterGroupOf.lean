import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterGroupSheaf
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.GroupRepresentatives

/-! # Character Group Of -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality

noncomputable section

/-!
# CartierDuality: base change of the actual commutative-group character sheaf
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u v w z

namespace CharacterGroupOf.Construction.CharacterGroupBaseChange

variable {C : Type u} [Category.{v} C] {C' : Type u} [Category.{v} C']

/-- Internal group-Hom sections with commutative target carry the
pointwise commutative group structure. -/
instance internalHomCommGroup (F : Cᵒᵖ ⥤ GrpCat.{w}) (K : Cᵒᵖ ⥤ CommGrpCat.{w}) (T : Cᵒᵖ) :
    CommGroup ((presheafHom F (K ⋙ forget₂ CommGrpCat GrpCat)).obj T) :=
  CharacterGroupSheaf.Construction.CharacterGroups.homCommGroup ((Over.forget T.unop).op ⋙ F) ((Over.forget T.unop).op ⋙ K)

/-- The pointwise group law on a restricted internal Hom, with
the associativity of functor composition made explicit for inference. -/
instance whiskeredInternalHomCommGroup (H : C' ⥤ C) (F : Cᵒᵖ ⥤ GrpCat.{w})
    (K : Cᵒᵖ ⥤ CommGrpCat.{w}) (T : C'ᵒᵖ) :
    CommGroup ((presheafHom (H.op ⋙ F) (H.op ⋙ K ⋙ forget₂ CommGrpCat GrpCat)).obj T) :=
  internalHomCommGroup (H.op ⋙ F) (H.op ⋙ K) T

/-- Precomposition on test categories preserves pointwise products
of internal group-Hom sections. -/
theorem whiskerMap_mul (H : C' ⥤ C) (F : Cᵒᵖ ⥤ GrpCat.{w}) (K : Cᵒᵖ ⥤ CommGrpCat.{w})
    (T : C'ᵒᵖ)
    (χ ψ : (presheafHom F (K ⋙ forget₂ CommGrpCat GrpCat)).obj (H.op.obj T)) :
    (CharacterBaseChange.Construction.Slices.presheafHomWhiskerMap H F (K ⋙ forget₂ CommGrpCat GrpCat)).app T (χ * ψ) =
      (CharacterBaseChange.Construction.Slices.presheafHomWhiskerMap H F (K ⋙ forget₂ CommGrpCat GrpCat)).app T χ *
        (CharacterBaseChange.Construction.Slices.presheafHomWhiskerMap H F (K ⋙ forget₂ CommGrpCat GrpCat)).app T ψ := rfl

/-- Changing source and target by natural group isomorphisms preserves
the pointwise multiplication of internal-Hom sections. -/
theorem congr_mul {F F' : Cᵒᵖ ⥤ GrpCat.{w}} {K K' : Cᵒᵖ ⥤ CommGrpCat.{w}}
    (a : F ≅ F') (b : K ⋙ forget₂ CommGrpCat GrpCat ≅ K' ⋙ forget₂ CommGrpCat GrpCat)
    (T : Cᵒᵖ) (χ ψ : (presheafHom F (K ⋙ forget₂ CommGrpCat GrpCat)).obj T) :
    (CharacterBaseChange.Construction.Slices.presheafHomCongr a b).hom.app T (χ * ψ) =
      (CharacterBaseChange.Construction.Slices.presheafHomCongr a b).hom.app T χ * (CharacterBaseChange.Construction.Slices.presheafHomCongr a b).hom.app T ψ := by
  apply NatTrans.ext
  funext U
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro x
  exact (b.hom.app (Opposite.op U.unop.left)).hom.map_mul _ _

/-- A multiplicative isomorphism of underlying type-valued functors
is an isomorphism of their commutative-group-valued functors. -/
def commGroupIsoOfTypeIso {F K : C ⥤ CommGrpCat.{w}}
    (e : F ⋙ forget CommGrpCat ≅ K ⋙ forget CommGrpCat)
    (he : ∀ (X : C) (x y : F.obj X), e.hom.app X (x * y) = e.hom.app X x * e.hom.app X y) :
    F ≅ K :=
  NatIso.ofComponents (fun X =>
    (show F.obj X ≃* K.obj X from
      { toEquiv := (e.app X).toEquiv
        map_mul' := he X }).toCommGrpIso) (by
    intro X Y f
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact congrArg (fun k : (F ⋙ forget CommGrpCat).obj X ⟶
      (K ⋙ forget CommGrpCat).obj Y => k x) (e.hom.naturality f))

/-- Transport a natural group isomorphism through natural component
equivalences, allowing the two models to live in different universes. -/
def isoViaEquivalences {F K : C ⥤ CommGrpCat.{w}} {F' K' : C ⥤ CommGrpCat.{z}}
    (e : F' ≅ K') (a : ∀ X, F.obj X ≃* F'.obj X) (b : ∀ X, K.obj X ≃* K'.obj X)
    (ha : ∀ {X Y} (f : X ⟶ Y) (x : F.obj X), a Y (F.map f x) = F'.map f (a X x))
    (hb : ∀ {X Y} (f : X ⟶ Y) (x : K.obj X), b Y (K.map f x) = K'.map f (b X x)) :
    F ≅ K :=
  NatIso.ofComponents (fun X =>
    ((a X).trans ((e.app X).commGroupIsoToMulEquiv.trans (b X).symm)).toCommGrpIso) (by
    intro X Y f
    apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply (b Y).injective
    change b Y ((b Y).symm (e.hom.app Y (a Y (F.map f x)))) =
      b Y (K.map f ((b X).symm (e.hom.app X (a X x))))
    have ht := hb f ((b X).symm (e.hom.app X (a X x)))
    have ht' := ht.trans (congrArg (K'.map f) ((b X).apply_symm_apply _))
    exact ((b Y).apply_symm_apply _).trans
      ((congrArg (e.hom.app Y) (ha f x)).trans
        ((e.hom.naturality_apply f (a X x)).trans ht'.symm)))

end CharacterGroupOf.Construction.CharacterGroupBaseChange

/-- The actual character base-change comparison preserves the
pointwise commutative group law, for arbitrary scheme base change. -/
theorem CharacterGroupOf.Construction.Schemes.characterBaseChangePresheafIso_mul {S T : Scheme.{u}} (f : T ⟶ S) (G : Grp (Over S))
    (U : (Over T)ᵒᵖ)
    (χ ψ : (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj ((Over.map f).op.obj U)) :
    (CharacterBaseChange.Construction.Schemes.characterBaseChangePresheafIso f G).hom.app U (χ * ψ) =
      (CharacterBaseChange.Construction.Schemes.characterBaseChangePresheafIso f G).hom.app U χ *
        (CharacterBaseChange.Construction.Schemes.characterBaseChangePresheafIso f G).hom.app U ψ := by
  let K := CharacterGroupSheaf.Construction.Schemes.commGroupPoints S (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S)
  let K' := CharacterGroupSheaf.Construction.Schemes.commGroupPoints T (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver T)
  let a := CharacterBaseChange.Construction.Schemes.pullbackGroupPointIso f G
  let b : ((Over.map f).op ⋙ K) ⋙ forget₂ CommGrpCat GrpCat ≅ K' ⋙ forget₂ CommGrpCat GrpCat :=
    CharacterBaseChange.Construction.Schemes.pullbackGroupPointIso f (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) ≪≫
      yonedaGrp.mapIso (SliceCharacters.Construction.Schemes.multiplicativeGroup_pullbackIso f)
  let c := CharacterBaseChange.Construction.Slices.presheafHomWhiskerMap (Over.map f) (yonedaGrp.obj G)
    (yonedaGrp.obj (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S))
  have hc := CharacterGroupOf.Construction.CharacterGroupBaseChange.whiskerMap_mul (Over.map f) (yonedaGrp.obj G) K U χ ψ
  have hb := CharacterGroupOf.Construction.CharacterGroupBaseChange.congr_mul a b U (c.app U χ) (c.app U ψ)
  change (CharacterBaseChange.Construction.Slices.presheafHomCongr a b).hom.app U (c.app U (χ * ψ)) =
    (CharacterBaseChange.Construction.Slices.presheafHomCongr a b).hom.app U (c.app U χ) *
      (CharacterBaseChange.Construction.Slices.presheafHomCongr a b).hom.app U (c.app U ψ)
  exact (congrArg ((CharacterBaseChange.Construction.Slices.presheafHomCongr a b).hom.app U) hc).trans hb

/-- Arbitrary base change identifies the actual commutative character
groups naturally on every test scheme. -/
def CharacterGroupOf.Construction.Schemes.characterBaseChangeCommGroupPresheafIso {S T : Scheme.{u}} (f : T ⟶ S) (G : Grp (Over S)) :
    (Over.map f).op ⋙ CharacterGroupSheaf.Construction.Schemes.characterCommGroupPresheaf S G ≅
      CharacterGroupSheaf.Construction.Schemes.characterCommGroupPresheaf T ((Over.pullback f).mapGrp.obj G) :=
  CharacterGroupOf.Construction.CharacterGroupBaseChange.commGroupIsoOfTypeIso (CharacterBaseChange.Construction.Schemes.characterBaseChangePresheafIso f G)
    (CharacterGroupOf.Construction.Schemes.characterBaseChangePresheafIso_mul f G)

/-- The actual fppf sheaf of commutative character groups commutes
with arbitrary scheme base change. -/
def CharacterGroupOf.Construction.Schemes.characterBaseChangeCommGroupIso {S T : Scheme.{u}} (f : T ⟶ S) (G : Grp (Over S)) :
    (Scheme.fppfTopology.overMapPullback CommGrpCat.{u + 1} f).obj (CharacterGroupSheaf.Construction.Schemes.characterCommGroupSheaf S G) ≅
      CharacterGroupSheaf.Construction.Schemes.characterCommGroupSheaf T ((Over.pullback f).mapGrp.obj G) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (CharacterGroupOf.Construction.Schemes.characterBaseChangeCommGroupPresheafIso f G)

/-- The small native character groups also commute with arbitrary
base change, through the same actual character comparison. -/
def CharacterGroupOf.Construction.Schemes.nativeCharacterBaseChangeCommGroupPresheafIso {S T : Scheme.{u}} (f : T ⟶ S)
    (G : Grp (Over S)) :
    (Over.map f).op ⋙ CharacterGroupSheaf.Construction.Schemes.nativeCharacterCommGroupPresheaf S G ≅
      CharacterGroupSheaf.Construction.Schemes.nativeCharacterCommGroupPresheaf T ((Over.pullback f).mapGrp.obj G) :=
  CharacterGroupOf.Construction.CharacterGroupBaseChange.isoViaEquivalences (CharacterGroupOf.Construction.Schemes.characterBaseChangeCommGroupPresheafIso f G)
    (fun U => CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv S G ((Over.map f).op.obj U))
    (CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv T ((Over.pullback f).mapGrp.obj G))
    (fun k χ => CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv_natural S G ((Over.map f).op.map k) χ)
    (fun k χ => CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv_natural T ((Over.pullback f).mapGrp.obj G) k χ)

/-- The native character-group sheaf commutes with arbitrary base change. -/
def CharacterGroupOf.Construction.Schemes.nativeCharacterBaseChangeCommGroupIso {S T : Scheme.{u}} (f : T ⟶ S) (G : Grp (Over S)) :
    (Scheme.fppfTopology.overMapPullback CommGrpCat.{u} f).obj (CharacterGroupSheaf.Construction.Schemes.nativeCharacterCommGroupSheaf S G) ≅
      CharacterGroupSheaf.Construction.Schemes.nativeCharacterCommGroupSheaf T ((Over.pullback f).mapGrp.obj G) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (CharacterGroupOf.Construction.Schemes.nativeCharacterBaseChangeCommGroupPresheafIso f G)

/-- Pullback of a native Cartier-dual representative represents the
characters of the pulled-back group, with all group laws retained. -/
def GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.baseChange {S T : Scheme.{u}} {G : Grp (Over S)}
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (f : T ⟶ S) :
    GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation T ((Over.pullback f).mapGrp.obj G) where
  dual := (Over.pullback f).mapGrp.obj D.dual
  commutative := by
    let : IsCommMonObj D.dual.X := D.commutative
    exact Functor.isCommMonObj_obj (F := Over.pullback f) (M := D.dual.X)
  finite := by
    let : IsFinite D.dual.X.hom := D.finite
    change IsFinite (CategoryTheory.Limits.pullback.snd D.dual.X.hom f)
    infer_instance
  flat := by
    let : Flat D.dual.X.hom := D.flat
    change Flat (CategoryTheory.Limits.pullback.snd D.dual.X.hom f)
    infer_instance
  finitelyPresented := by
    let : LocallyOfFinitePresentation D.dual.X.hom := D.finitelyPresented
    change LocallyOfFinitePresentation (CategoryTheory.Limits.pullback.snd D.dual.X.hom f)
    infer_instance
  pointsIso := (CharacterBaseChange.Construction.Schemes.pullbackGroupPointIso f D.dual).symm ≪≫
    Functor.isoWhiskerLeft (Over.map f).op D.pointsIso ≪≫
      Functor.isoWhiskerRight (CharacterGroupOf.Construction.Schemes.nativeCharacterBaseChangeCommGroupPresheafIso f G)
        (forget₂ CommGrpCat GrpCat)

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality
