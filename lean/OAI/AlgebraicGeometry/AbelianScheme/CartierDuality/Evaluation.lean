import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.GroupRepresentatives

/-! # Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality

noncomputable section

/-!
# CartierDuality: canonical evaluation of characters
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u v w

namespace Evaluation.Construction.CharacterEvaluation

variable {C : Type u} [Category.{v} C] {F K : Cᵒᵖ ⥤ GrpCat.{w}}

/-- Naturality of a group-valued transformation into a functor of
commutative groups, with forgetting made explicit. -/
theorem groupTransformation_natural {H : Cᵒᵖ ⥤ CommGrpCat.{w}}
    (a : F ⟶ H ⋙ forget₂ CommGrpCat GrpCat) {T U : Cᵒᵖ} (f : T ⟶ U) (x : F.obj T) :
    a.app U (F.map f x) = H.map f (a.app T x) :=
  a.naturality_apply f x

/-- Evaluate an internal-Hom section at the identity test morphism. -/
def value {T : C} (χ : (presheafHom F K).obj (Opposite.op T)) :
    F.obj (Opposite.op T) →* K.obj (Opposite.op T) :=
  (χ.app (Opposite.op (Over.mk (𝟙 T)))).hom

/-- Restriction followed by evaluation is evaluation at the restricted
test object. -/
theorem value_restrict {T U : C} (f : U ⟶ T)
    (χ : (presheafHom F K).obj (Opposite.op T)) (x : F.obj (Opposite.op U)) :
    value ((presheafHom F K).map f.op χ) x = χ.app (Opposite.op (Over.mk f)) x :=
  congrArg (fun h => h.hom x) (presheafHom_map_app_op_mk_id f χ)

/-- Evaluation commutes with restriction of both its arguments. -/
theorem value_natural {T U : C} (f : U ⟶ T)
    (χ : (presheafHom F K).obj (Opposite.op T)) (x : F.obj (Opposite.op T)) :
    value ((presheafHom F K).map f.op χ) (F.map f.op x) =
      K.map f.op (value χ x) := by
  exact (value_restrict f χ _).trans
    (χ.naturality_apply (Over.homMk f : Over.mk f ⟶ Over.mk (𝟙 T)).op x)

/-- A group-valued Yoneda transformation is represented by a group
morphism with exactly its specified action on points. -/
theorem yonedaGrp_preimage_points [CartesianMonoidalCategory C]
    {G H : Grp C} (a : yonedaGrp.obj G ⟶ yonedaGrp.obj H) (T : C) (x : T ⟶ G.X) :
    x ≫ (yonedaGrpFullyFaithful.preimage a).hom.hom = a.app (Opposite.op T) x :=
  congrArg
    (fun b : yonedaGrp.obj G ⟶ yonedaGrp.obj H => (b.app (Opposite.op T)).hom x)
      (yonedaGrpFullyFaithful.map_preimage a)

/-- Build a group-valued Yoneda transformation from natural homomorphisms on points. -/
def pointTransformation [CartesianMonoidalCategory C] {G H : Grp C}
    (p : ∀ T : C, (T ⟶ G.X) →* (T ⟶ H.X))
    (hp : ∀ {T U : C} (f : U ⟶ T) (x : T ⟶ G.X), p U (f ≫ x) = f ≫ p T x) :
    yonedaGrp.obj G ⟶ yonedaGrp.obj H where
  app T := GrpCat.ofHom (p T.unop)
  naturality := by
    intro T U f
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    exact hp f.unop x

/-- The component formula for a pointwise-defined group transformation. -/
theorem pointTransformation_app [CartesianMonoidalCategory C] {G H : Grp C}
    (p : ∀ T : C, (T ⟶ G.X) →* (T ⟶ H.X))
    (hp : ∀ {T U : C} (f : U ⟶ T) (x : T ⟶ G.X), p U (f ≫ x) = f ≫ p T x) (T : C) :
    ((pointTransformation p hp).app (Opposite.op T)).hom = p T := rfl

end Evaluation.Construction.CharacterEvaluation

variable {S : Scheme.{u}} {G : Grp (Over S)}

/-- The representing point-character bijection, retaining pointwise
multiplication on actual character sections. -/
def GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.sectionEquiv (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G)
    (T : Over S) : (T ⟶ D.dual.X) ≃* (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op T) :=
  (CategoryTheory.Iso.groupIsoToMulEquiv (D.pointsIso.app (Opposite.op T))).trans
    (CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv S G (Opposite.op T))

/-- The point-character group equivalence uses the specified group
representation followed by the size comparison. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.sectionEquiv_apply
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (T : Over S) (d : T ⟶ D.dual.X) :
    D.sectionEquiv T d = CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv S G (Opposite.op T)
      (D.pointsIso.hom.app (Opposite.op T) d) := rfl

/-- The representing point-character equivalence is natural for every
morphism of test schemes. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.sectionEquiv_natural
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) {T U : Over S} (f : U ⟶ T) (d : T ⟶ D.dual.X) :
    D.sectionEquiv U (f ≫ d) =
      (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.map f.op (D.sectionEquiv T d) := by
  rw [D.sectionEquiv_apply, D.sectionEquiv_apply]
  have hd : D.pointsIso.hom.app (Opposite.op U) (f ≫ d) =
      (CharacterGroupSheaf.Construction.Schemes.nativeCharacterCommGroupPresheaf S G).map f.op
        (D.pointsIso.hom.app (Opposite.op T) d) :=
    Evaluation.Construction.CharacterEvaluation.groupTransformation_natural D.pointsIso.hom f.op d
  exact (congrArg (CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv S G (Opposite.op U))
    hd).trans
      (CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv_natural S G f.op _)

/-- The canonical Cartier pairing on scheme-valued points. -/
def GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.evaluationValue (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G)
    (T : Over S) (d : T ⟶ D.dual.X) (x : T ⟶ G.X) :
    T ⟶ (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X :=
  Evaluation.Construction.CharacterEvaluation.value (D.sectionEquiv T d) x

/-- Cartier evaluation is multiplicative in the character. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.evaluationValue_mul_left
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (T : Over S)
    (a b : T ⟶ D.dual.X) (x : T ⟶ G.X) :
    D.evaluationValue T (a * b) x = D.evaluationValue T a x * D.evaluationValue T b x := by
  exact congrArg
    (fun χ : (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op T) => Evaluation.Construction.CharacterEvaluation.value χ x)
      ((D.sectionEquiv T).map_mul a b)

/-- The identity character evaluates to the identity. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.evaluationValue_one_left
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (T : Over S) (x : T ⟶ G.X) :
    D.evaluationValue T 1 x = 1 := by
  exact congrArg
    (fun χ : (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op T) => Evaluation.Construction.CharacterEvaluation.value χ x)
      (D.sectionEquiv T).map_one

/-- Cartier evaluation is multiplicative in the original group point. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.evaluationValue_mul_right
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (T : Over S)
    (d : T ⟶ D.dual.X) (x y : T ⟶ G.X) :
    D.evaluationValue T d (x * y) = D.evaluationValue T d x * D.evaluationValue T d y :=
  (Evaluation.Construction.CharacterEvaluation.value (D.sectionEquiv T d)).map_mul x y

/-- Every character evaluates to the identity at the identity group point. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.evaluationValue_one_right
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (T : Over S) (d : T ⟶ D.dual.X) :
    D.evaluationValue T d 1 = 1 :=
  (Evaluation.Construction.CharacterEvaluation.value (D.sectionEquiv T d)).map_one

/-- Cartier evaluation is natural on all test schemes. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.evaluationValue_natural
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) {T U : Over S} (f : U ⟶ T)
    (d : T ⟶ D.dual.X) (x : T ⟶ G.X) :
    D.evaluationValue U (f ≫ d) (f ≫ x) = f ≫ D.evaluationValue T d x := by
  exact (congrArg
    (fun χ : (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op U) => Evaluation.Construction.CharacterEvaluation.value χ (f ≫ x))
    (D.sectionEquiv_natural f d)).trans
      (Evaluation.Construction.CharacterEvaluation.value_natural (F := yonedaGrp.obj G)
        (K := yonedaGrp.obj (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S)) f (D.sectionEquiv T d) x)

/-- Evaluating characters at a group point gives a character of the
dual group over the same test scheme. -/
def GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.evaluationCharacter
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (T : Over S) (x : T ⟶ G.X) :
    (CharacterSheaf.Construction.Schemes.characterSheaf S D.dual).obj.obj (Opposite.op T) where
  app U := GrpCat.ofHom
    { toFun := fun d => D.evaluationValue U.unop.left d (U.unop.hom ≫ x)
      map_one' := D.evaluationValue_one_left U.unop.left (U.unop.hom ≫ x)
      map_mul' a b := D.evaluationValue_mul_left U.unop.left a b (U.unop.hom ≫ x) }
  naturality := by
    intro U V f
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro d
    change D.evaluationValue V.unop.left (f.unop.left ≫ d) (V.unop.hom ≫ x) =
      f.unop.left ≫ D.evaluationValue U.unop.left d (U.unop.hom ≫ x)
    have hw : V.unop.hom ≫ x = f.unop.left ≫ (U.unop.hom ≫ x) :=
      (congrArg (fun k => k ≫ x) f.unop.w.symm).trans
        (Category.assoc f.unop.left U.unop.hom x)
    exact (congrArg (D.evaluationValue V.unop.left (f.unop.left ≫ d)) hw).trans
      (D.evaluationValue_natural f.unop.left d (U.unop.hom ≫ x))

/-- The character induced by the identity point is trivial. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.evaluationCharacter_one
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (T : Over S) :
    D.evaluationCharacter T 1 = 1 := by
  apply NatTrans.ext
  funext U
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro d
  change D.evaluationValue U.unop.left d (U.unop.hom ≫ 1) = 1
  exact (congrArg (D.evaluationValue U.unop.left d)
    (((yonedaGrp.obj G).map U.unop.hom.op).hom.map_one)).trans
      (D.evaluationValue_one_right U.unop.left d)

/-- Evaluation into the double character group is a group homomorphism. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.evaluationCharacter_mul
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (T : Over S) (x y : T ⟶ G.X) :
    D.evaluationCharacter T (x * y) = D.evaluationCharacter T x * D.evaluationCharacter T y := by
  apply NatTrans.ext
  funext U
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro d
  change D.evaluationValue U.unop.left d (U.unop.hom ≫ (x * y)) =
    D.evaluationValue U.unop.left d (U.unop.hom ≫ x) *
      D.evaluationValue U.unop.left d (U.unop.hom ≫ y)
  exact (congrArg (D.evaluationValue U.unop.left d)
    (((yonedaGrp.obj G).map U.unop.hom.op).hom.map_mul x y)).trans
      (D.evaluationValue_mul_right U.unop.left d (U.unop.hom ≫ x) (U.unop.hom ≫ y))

/-- The evaluation character restricts to the evaluation character of
the restricted group point. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.evaluationCharacter_natural
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) {T U : Over S} (f : U ⟶ T) (x : T ⟶ G.X) :
    D.evaluationCharacter U (f ≫ x) =
      (CharacterSheaf.Construction.Schemes.characterSheaf S D.dual).obj.map f.op (D.evaluationCharacter T x) := by
  apply NatTrans.ext
  funext V
  apply GrpCat.hom_ext
  apply MonoidHom.ext
  intro d
  change D.evaluationValue V.unop.left d (V.unop.hom ≫ f ≫ x) =
    D.evaluationValue V.unop.left d ((V.unop.hom ≫ f) ≫ x)
  exact congrArg (D.evaluationValue V.unop.left d) (Category.assoc V.unop.hom f x).symm

/-- Evaluation is a homomorphism from group points to characters of
the Cartier-dual group. -/
def GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.evaluationCharacterHom
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (T : Over S) :
    (T ⟶ G.X) →* (CharacterSheaf.Construction.Schemes.characterSheaf S D.dual).obj.obj (Opposite.op T) where
  toFun := D.evaluationCharacter T
  map_one' := D.evaluationCharacter_one T
  map_mul' := D.evaluationCharacter_mul T

/-- The canonical bidual evaluation on group-valued points, obtained
by representing the transposed evaluation character. -/
def GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.bidualPointHom
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S D.dual)
    (T : Over S) : (T ⟶ G.X) →* (T ⟶ E.dual.X) where
  toFun := fun x => (E.sectionEquiv T).symm (D.evaluationCharacter T x)
  map_one' := (congrArg (E.sectionEquiv T).symm (D.evaluationCharacter_one T)).trans
    (E.sectionEquiv T).symm.map_one
  map_mul' x y := (congrArg (E.sectionEquiv T).symm (D.evaluationCharacter_mul T x y)).trans
    ((E.sectionEquiv T).symm.map_mul _ _)

/-- Bidual evaluation of points commutes with restriction. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.bidualPointHom_natural
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S D.dual)
    {T U : Over S} (f : U ⟶ T) (x : T ⟶ G.X) :
    D.bidualPointHom E U (f ≫ x) = f ≫ D.bidualPointHom E T x := by
    apply (E.sectionEquiv U).injective
    change E.sectionEquiv U
        ((E.sectionEquiv U).symm (D.evaluationCharacter U (f ≫ x))) =
      E.sectionEquiv U
        (f ≫ (E.sectionEquiv T).symm (D.evaluationCharacter T x))
    rw [MulEquiv.apply_symm_apply, E.sectionEquiv_natural, MulEquiv.apply_symm_apply]
    exact D.evaluationCharacter_natural f x

/-- The pointwise bidual homomorphisms form a natural transformation. -/
def GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.bidualPointMap
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S D.dual) :
    yonedaGrp.obj G ⟶ yonedaGrp.obj E.dual :=
  Evaluation.Construction.CharacterEvaluation.pointTransformation (D.bidualPointHom E) (D.bidualPointHom_natural E)

/-- Canonical bidual evaluation as an actual morphism of group schemes. -/
def GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.bidualEvaluation
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S D.dual) :
    G ⟶ E.dual :=
  yonedaGrpFullyFaithful.preimage (D.bidualPointMap E)

/-- The component of the bidual transformation is its specified group homomorphism. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.bidualPointMap_app
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S D.dual)
    (T : Over S) :
    ((D.bidualPointMap E).app (Opposite.op T)).hom = D.bidualPointHom E T :=
  Evaluation.Construction.CharacterEvaluation.pointTransformation_app (D.bidualPointHom E) (D.bidualPointHom_natural E) T

/-- The bidual point homomorphism sends a point to its represented evaluation character. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.bidualPointHom_apply
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S D.dual)
    (T : Over S) (x : T ⟶ G.X) :
    D.bidualPointHom E T x =
      (E.sectionEquiv T).symm (D.evaluationCharacter T x) := rfl

/-- The native bidual morphism has exactly the prescribed evaluation
action on every scheme-valued group point. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.bidualEvaluation_points
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S D.dual)
    (T : Over S) (x : T ⟶ G.X) :
    x ≫ (D.bidualEvaluation E).hom.hom =
      (E.sectionEquiv T).symm (D.evaluationCharacter T x) := by
  have h := Evaluation.Construction.CharacterEvaluation.yonedaGrp_preimage_points (D.bidualPointMap E) T x
  exact h.trans ((congrArg (fun f => f x) (D.bidualPointMap_app E T)).trans
    (D.bidualPointHom_apply E T x))

/-- The bidual image of a point is the character evaluating each
character at that point. This identifies the native map canonically. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.bidualEvaluation_character
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S D.dual)
    (T : Over S) (x : T ⟶ G.X) :
    E.sectionEquiv T (x ≫ (D.bidualEvaluation E).hom.hom) = D.evaluationCharacter T x := by
  exact (congrArg (E.sectionEquiv T) (D.bidualEvaluation_points E T x)).trans
    ((E.sectionEquiv T).apply_symm_apply _)

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality
