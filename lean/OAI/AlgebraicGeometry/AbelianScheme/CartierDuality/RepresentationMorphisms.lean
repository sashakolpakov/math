import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Evaluation

/-! # Representation Morphisms -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality

noncomputable section

/-!
# CartierDuality: native morphisms between Cartier-dual representatives
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u v

namespace RepresentationMorphisms.Construction.CharacterEvaluation

/-- The morphism represented by natural point homomorphisms acts by
those homomorphisms on every test object. -/
theorem pointTransformation_preimage_points {C : Type u} [Category.{v} C]
    [CartesianMonoidalCategory C] {G H : Grp C}
    (p : ∀ T : C, (T ⟶ G.X) →* (T ⟶ H.X))
    (hp : ∀ {T U : C} (f : U ⟶ T) (x : T ⟶ G.X), p U (f ≫ x) = f ≫ p T x)
    (T : C) (x : T ⟶ G.X) :
    x ≫ (yonedaGrpFullyFaithful.preimage (Evaluation.Construction.CharacterEvaluation.pointTransformation p hp)).hom.hom = p T x :=
  (Evaluation.Construction.CharacterEvaluation.yonedaGrp_preimage_points (Evaluation.Construction.CharacterEvaluation.pointTransformation p hp) T x).trans
    (congrArg (fun f : (T ⟶ G.X) →* (T ⟶ H.X) => f x) (Evaluation.Construction.CharacterEvaluation.pointTransformation_app p hp T))

end RepresentationMorphisms.Construction.CharacterEvaluation

variable {S : Scheme.{u}} {G H : Grp (Over S)}

/-- Restriction of characters is a homomorphism for their actual
pointwise commutative group laws. -/
def RepresentationMorphisms.Construction.Schemes.characterRestrictionHom (f : H ⟶ G) (T : Over S) :
    (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op T) →*
      (CharacterSheaf.Construction.Schemes.characterSheaf S H).obj.obj (Opposite.op T) where
  toFun := (CharacterSheaf.Construction.Schemes.characterRestriction f).hom.app (Opposite.op T)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Character restriction commutes with restriction of the test scheme. -/
theorem RepresentationMorphisms.Construction.Schemes.characterRestrictionHom_natural (f : H ⟶ G) {T U : Over S} (p : U ⟶ T)
    (χ : (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op T)) :
    RepresentationMorphisms.Construction.Schemes.characterRestrictionHom f U ((CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.map p.op χ) =
      (CharacterSheaf.Construction.Schemes.characterSheaf S H).obj.map p.op (RepresentationMorphisms.Construction.Schemes.characterRestrictionHom f T χ) :=
  congrArg (fun k : (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op T) ⟶
    (CharacterSheaf.Construction.Schemes.characterSheaf S H).obj.obj (Opposite.op U) => k χ)
      ((CharacterSheaf.Construction.Schemes.characterRestriction f).hom.naturality p.op)

/-- Restriction along the identity does not change a character. -/
theorem RepresentationMorphisms.Construction.Schemes.characterRestrictionHom_id (T : Over S)
    (χ : (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op T)) :
    RepresentationMorphisms.Construction.Schemes.characterRestrictionHom (𝟙 G) T χ = χ :=
  congrArg (fun a : CharacterSheaf.Construction.Schemes.characterSheaf S G ⟶ CharacterSheaf.Construction.Schemes.characterSheaf S G => a.hom.app (Opposite.op T) χ)
    (CharacterFunctor.Construction.Schemes.characterRestriction_id S G)

/-- Successive restrictions are restriction along the composite. -/
theorem RepresentationMorphisms.Construction.Schemes.characterRestrictionHom_comp {K : Grp (Over S)} (f : H ⟶ G) (g : K ⟶ H)
    (T : Over S) (χ : (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op T)) :
    RepresentationMorphisms.Construction.Schemes.characterRestrictionHom (g ≫ f) T χ =
      RepresentationMorphisms.Construction.Schemes.characterRestrictionHom g T (RepresentationMorphisms.Construction.Schemes.characterRestrictionHom f T χ) :=
  congrArg (fun a : CharacterSheaf.Construction.Schemes.characterSheaf S G ⟶ CharacterSheaf.Construction.Schemes.characterSheaf S K => a.hom.app (Opposite.op T) χ)
    (CharacterFunctor.Construction.Schemes.characterRestriction_comp g f)

/-- Restriction along a group morphism gives homomorphisms between
the points of its two Cartier-dual representatives. -/
def GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.dualMapPointHom
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S H)
    (f : H ⟶ G) (T : Over S) : (T ⟶ D.dual.X) →* (T ⟶ E.dual.X) where
  toFun := fun d => (E.sectionEquiv T).symm (RepresentationMorphisms.Construction.Schemes.characterRestrictionHom f T (D.sectionEquiv T d))
  map_one' := by simp only [map_one]
  map_mul' a b := by simp only [map_mul]

/-- The induced homomorphisms of dual points commute with every
morphism of test schemes. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.dualMapPointHom_natural
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S H)
    (f : H ⟶ G) {T U : Over S} (p : U ⟶ T) (d : T ⟶ D.dual.X) :
    D.dualMapPointHom E f U (p ≫ d) = p ≫ D.dualMapPointHom E f T d := by
  apply (E.sectionEquiv U).injective
  change E.sectionEquiv U ((E.sectionEquiv U).symm
      (RepresentationMorphisms.Construction.Schemes.characterRestrictionHom f U (D.sectionEquiv U (p ≫ d)))) =
    E.sectionEquiv U (p ≫ (E.sectionEquiv T).symm
      (RepresentationMorphisms.Construction.Schemes.characterRestrictionHom f T (D.sectionEquiv T d)))
  rw [MulEquiv.apply_symm_apply, E.sectionEquiv_natural, MulEquiv.apply_symm_apply]
  exact (congrArg (RepresentationMorphisms.Construction.Schemes.characterRestrictionHom f U) (D.sectionEquiv_natural p d)).trans
    (RepresentationMorphisms.Construction.Schemes.characterRestrictionHom_natural f p (D.sectionEquiv T d))

/-- The native contravariant Cartier-dual morphism induced by a
group-scheme homomorphism, defined through actual character restriction. -/
def GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.dualMap
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S H)
    (f : H ⟶ G) : D.dual ⟶ E.dual :=
  yonedaGrpFullyFaithful.preimage
    (Evaluation.Construction.CharacterEvaluation.pointTransformation (D.dualMapPointHom E f) (D.dualMapPointHom_natural E f))

/-- The native dual morphism acts on points by restricting the
corresponding character along the original group morphism. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.dualMap_points
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S H)
    (f : H ⟶ G) (T : Over S) (d : T ⟶ D.dual.X) :
    d ≫ (D.dualMap E f).hom.hom =
      (E.sectionEquiv T).symm (RepresentationMorphisms.Construction.Schemes.characterRestrictionHom f T (D.sectionEquiv T d)) :=
  RepresentationMorphisms.Construction.CharacterEvaluation.pointTransformation_preimage_points (D.dualMapPointHom E f)
    (D.dualMapPointHom_natural E f) T d

/-- The character of the image under the native dual morphism is
the restriction of the original character. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.dualMap_character
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S H)
    (f : H ⟶ G) (T : Over S) (d : T ⟶ D.dual.X) :
    E.sectionEquiv T (d ≫ (D.dualMap E f).hom.hom) =
      RepresentationMorphisms.Construction.Schemes.characterRestrictionHom f T (D.sectionEquiv T d) :=
  (congrArg (E.sectionEquiv T) (D.dualMap_points E f T d)).trans
    ((E.sectionEquiv T).apply_symm_apply _)

/-- Morphisms into a character representative are determined by
the character of their underlying morphism. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.hom_ext
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) {K : Grp (Over S)} (f g : K ⟶ D.dual)
    (h : D.sectionEquiv K.X f.hom.hom = D.sectionEquiv K.X g.hom.hom) : f = g :=
  Grp.hom_ext _ _ ((D.sectionEquiv K.X).injective h)

/-- The character associated with a dual morphism is restriction of
the universal character of its source. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.dualMap_character_id
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S H) (f : H ⟶ G) :
    E.sectionEquiv D.dual.X (D.dualMap E f).hom.hom =
      RepresentationMorphisms.Construction.Schemes.characterRestrictionHom f D.dual.X (D.sectionEquiv D.dual.X (𝟙 D.dual.X)) :=
  (congrArg (E.sectionEquiv D.dual.X) (Category.id_comp (D.dualMap E f).hom.hom)).symm.trans
    (D.dualMap_character E f D.dual.X (𝟙 D.dual.X))

/-- Native Cartier duality preserves identity morphisms. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.dualMap_id (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) :
    D.dualMap D (𝟙 G) = 𝟙 D.dual := by
  apply D.hom_ext
  exact (D.dualMap_character_id D (𝟙 G)).trans
    (RepresentationMorphisms.Construction.Schemes.characterRestrictionHom_id D.dual.X (D.sectionEquiv D.dual.X (𝟙 D.dual.X)))

/-- Native Cartier duality reverses composition of group-scheme morphisms. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.dualMap_comp {K : Grp (Over S)}
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S H)
    (F : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S K) (f : H ⟶ G) (g : K ⟶ H) :
    D.dualMap F (g ≫ f) = D.dualMap E f ≫ E.dualMap F g := by
  apply F.hom_ext
  have hleft := D.dualMap_character_id F (g ≫ f)
  have hright := E.dualMap_character F g D.dual.X (D.dualMap E f).hom.hom
  have hmid := congrArg (RepresentationMorphisms.Construction.Schemes.characterRestrictionHom g D.dual.X) (D.dualMap_character_id E f)
  have hcomp := RepresentationMorphisms.Construction.Schemes.characterRestrictionHom_comp f g D.dual.X (D.sectionEquiv D.dual.X (𝟙 D.dual.X))
  exact hleft.trans (hcomp.trans (hright.trans hmid).symm)

/-- Isomorphic source group schemes have canonically isomorphic
Cartier-dual group representatives. -/
def GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.dualMapIso
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S H) (e : H ≅ G) :
    D.dual ≅ E.dual where
  hom := D.dualMap E e.hom
  inv := E.dualMap D e.inv
  hom_inv_id := (D.dualMap_comp E D e.hom e.inv).symm.trans
    ((congrArg (fun f => D.dualMap D f) e.inv_hom_id).trans D.dualMap_id)
  inv_hom_id := (E.dualMap_comp D E e.inv e.hom).symm.trans
    ((congrArg (fun f => E.dualMap E f) e.hom_inv_id).trans E.dualMap_id)

/-- Two representations of the same character groups are canonically
isomorphic as native group schemes. -/
def GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.uniqueIso
    (D E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) : D.dual ≅ E.dual :=
  D.dualMapIso E (Iso.refl G)

/-- The canonical isomorphism of representatives preserves the actual
character associated with every test-scheme point. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.uniqueIso_character
    (D E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (T : Over S) (d : T ⟶ D.dual.X) :
    E.sectionEquiv T (d ≫ (D.uniqueIso E).hom.hom.hom) = D.sectionEquiv T d :=
  (D.dualMap_character E (𝟙 G) T d).trans (RepresentationMorphisms.Construction.Schemes.characterRestrictionHom_id T (D.sectionEquiv T d))

/-- Evaluating a restricted character is evaluating the original
character at the image of the group point. -/
theorem RepresentationMorphisms.Construction.Schemes.characterRestrictionHom_value (f : H ⟶ G) (T : Over S)
    (χ : (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op T)) (x : T ⟶ H.X) :
    Evaluation.Construction.CharacterEvaluation.value (RepresentationMorphisms.Construction.Schemes.characterRestrictionHom f T χ) x =
      Evaluation.Construction.CharacterEvaluation.value χ (x ≫ f.hom.hom) := rfl

/-- The native dual map is adjoint to the original group morphism
for the actual Cartier evaluation pairings. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.dualMap_evaluation
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S H)
    (f : H ⟶ G) (T : Over S) (d : T ⟶ D.dual.X) (x : T ⟶ H.X) :
    E.evaluationValue T (d ≫ (D.dualMap E f).hom.hom) x =
      D.evaluationValue T d (x ≫ f.hom.hom) :=
  (congrArg
    (fun χ : (CharacterSheaf.Construction.Schemes.characterSheaf S H).obj.obj (Opposite.op T) => Evaluation.Construction.CharacterEvaluation.value χ x)
      (D.dualMap_character E f T d)).trans (RepresentationMorphisms.Construction.Schemes.characterRestrictionHom_value f T (D.sectionEquiv T d) x)

/-- Pulling an evaluation character back along the native dual map
evaluates characters at the image under the original morphism. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.evaluationCharacter_dualMap
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S H)
    (f : H ⟶ G) (T : Over S) (x : T ⟶ H.X) :
    RepresentationMorphisms.Construction.Schemes.characterRestrictionHom (D.dualMap E f) T (E.evaluationCharacter T x) =
      D.evaluationCharacter T (x ≫ f.hom.hom) := by
  apply NatTrans.ext
  funext U
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro d
  change E.evaluationValue U.unop.left (d ≫ (D.dualMap E f).hom.hom) (U.unop.hom ≫ x) =
    D.evaluationValue U.unop.left d (U.unop.hom ≫ x ≫ f.hom.hom)
  exact (D.dualMap_evaluation E f U.unop.left d (U.unop.hom ≫ x)).trans
    (congrArg (D.evaluationValue U.unop.left d) (Category.assoc U.unop.hom x f.hom.hom))

/-- The character of the native bidual evaluation morphism is
evaluation at the universal point of the original group scheme. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.bidualEvaluation_character_id
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (F : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S D.dual) :
    F.sectionEquiv G.X (D.bidualEvaluation F).hom.hom = D.evaluationCharacter G.X (𝟙 G.X) :=
  (congrArg (F.sectionEquiv G.X) (Category.id_comp (D.bidualEvaluation F).hom.hom)).symm.trans
    (D.bidualEvaluation_character F G.X (𝟙 G.X))

/-- Canonical bidual evaluation is natural with respect to native
group-scheme morphisms and the induced contravariant dual morphisms. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.bidualEvaluation_natural
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S H)
    (F : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S D.dual) (K : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S E.dual)
    (f : H ⟶ G) :
    E.bidualEvaluation K ≫ K.dualMap F (D.dualMap E f) = f ≫ D.bidualEvaluation F := by
  apply F.hom_ext
  have hl := K.dualMap_character F (D.dualMap E f) H.X (E.bidualEvaluation K).hom.hom
  have hm := congrArg (RepresentationMorphisms.Construction.Schemes.characterRestrictionHom (D.dualMap E f) H.X)
    (E.bidualEvaluation_character_id K)
  have hr := D.evaluationCharacter_dualMap E f H.X (𝟙 H.X)
  have hi := congrArg (D.evaluationCharacter H.X) (Category.id_comp f.hom.hom)
  have he := D.bidualEvaluation_character F H.X f.hom.hom
  exact hl.trans (hm.trans (hr.trans (hi.trans he.symm)))

/-- Perfection of canonical bidual evaluation transports across
isomorphic presentations of the original group scheme, with arbitrary
choices of its first and second character representatives. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.bidualEvaluation_isIso_of_sourceIso
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S H)
    (F : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S D.dual) (K : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S E.dual)
    (e : H ≅ G) [IsIso (D.bidualEvaluation F)] : IsIso (E.bidualEvaluation K) := by
  let c := K.dualMap F (D.dualMap E e.hom)
  let hc : IsIso c := (K.dualMapIso F (D.dualMapIso E e)).isIso_hom
  have hfac := D.bidualEvaluation_natural E F K e.hom
  let hright : IsIso (e.hom ≫ D.bidualEvaluation F) := inferInstance
  let hleft : IsIso (E.bidualEvaluation K ≫ c) := (congrArg IsIso hfac).mpr hright
  exact IsIso.of_isIso_comp_right (E.bidualEvaluation K) c

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality
