import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterGroupOf
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.BidualCriterionEq

/-! # Evaluation Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality

noncomputable section

/-!
# CartierDuality: evaluation and biduality under arbitrary base change
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u v w z

namespace EvaluationBaseChange.Construction.CharacterEvaluation

variable {C : Type u} [Category.{v} C] {C' : Type u} [Category.{v} C']

/-- Evaluation of an internal Hom commutes with changing the source
and target presheaves by isomorphisms. -/
theorem value_congr {F F' K K' : Cᵒᵖ ⥤ GrpCat.{w}} (a : F ≅ F') (b : K ≅ K')
    (T : C) (χ : (presheafHom F K).obj (Opposite.op T)) (x : F'.obj (Opposite.op T)) :
    Evaluation.Construction.CharacterEvaluation.value ((CharacterBaseChange.Construction.Slices.presheafHomCongr a b).hom.app (Opposite.op T) χ) x =
      b.hom.app (Opposite.op T) (Evaluation.Construction.CharacterEvaluation.value χ (a.inv.app (Opposite.op T) x)) := rfl

/-- Evaluation of a restricted character is the original evaluation. -/
theorem value_whisker (H : C' ⥤ C) (F K : Cᵒᵖ ⥤ GrpCat.{w}) (T : C')
    (χ : (presheafHom F K).obj (Opposite.op (H.obj T)))
    (x : F.obj (Opposite.op (H.obj T))) :
    Evaluation.Construction.CharacterEvaluation.value ((CharacterBaseChange.Construction.Slices.presheafHomWhiskerMap H F K).app (Opposite.op T) χ) x = Evaluation.Construction.CharacterEvaluation.value χ x := by
  change χ.app (Opposite.op (Over.mk (H.map (𝟙 T)))) x =
    χ.app (Opposite.op (Over.mk (𝟙 (H.obj T)))) x
  exact congrArg (fun k : H.obj T ⟶ H.obj T =>
    (show K.obj (Opposite.op (H.obj T)) from χ.app (Opposite.op (Over.mk k)) x)) (H.map_id T)

end EvaluationBaseChange.Construction.CharacterEvaluation

namespace EvaluationBaseChange.Construction.CharacterGroupBaseChange

variable {C : Type u} [Category.{v} C]

/-- The transported isomorphism realizes the original component map. -/
theorem isoViaEquivalences_apply {F K : C ⥤ CommGrpCat.{w}} {F' K' : C ⥤ CommGrpCat.{z}}
    (e : F' ≅ K') (a : ∀ X, F.obj X ≃* F'.obj X) (b : ∀ X, K.obj X ≃* K'.obj X)
    (ha : ∀ {X Y} (f : X ⟶ Y) (x : F.obj X), a Y (F.map f x) = F'.map f (a X x))
    (hb : ∀ {X Y} (f : X ⟶ Y) (x : K.obj X), b Y (K.map f x) = K'.map f (b X x))
    (X : C) (x : F.obj X) :
    b X ((CharacterGroupOf.Construction.CharacterGroupBaseChange.isoViaEquivalences e a b ha hb).hom.app X x) = e.hom.app X (a X x) :=
  (b X).apply_symm_apply _

end EvaluationBaseChange.Construction.CharacterGroupBaseChange

/-- The canonical comparison of multiplicative-group points under
scheme base change. -/
def EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange {S T : Scheme.{u}} (f : T ⟶ S) (U : Over T) :
    ((Over.map f).obj U ⟶ (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S).X) ≃*
      (U ⟶ (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver T).X) :=
  (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) U).trans
    ((yonedaGrp.mapIso (SliceCharacters.Construction.Schemes.multiplicativeGroup_pullbackIso f)).app (Opposite.op U)).groupIsoToMulEquiv

/-- The actual character base-change isomorphism preserves evaluation,
using the canonical pullback comparisons for both kinds of points. -/
theorem EvaluationBaseChange.Construction.Schemes.characterBaseChange_value {S T : Scheme.{u}} (f : T ⟶ S) (G : Grp (Over S))
    (U : Over T) (χ : (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op ((Over.map f).obj U)))
    (x : U ⟶ ((Over.pullback f).mapGrp.obj G).X) :
    Evaluation.Construction.CharacterEvaluation.value ((CharacterBaseChange.Construction.Schemes.characterBaseChangePresheafIso f G).hom.app (Opposite.op U) χ) x =
      EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange f U
        (Evaluation.Construction.CharacterEvaluation.value χ ((CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f G U).symm x)) := by
  let a := CharacterBaseChange.Construction.Schemes.pullbackGroupPointIso f G
  let b := CharacterBaseChange.Construction.Schemes.pullbackGroupPointIso f (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S) ≪≫
    yonedaGrp.mapIso (SliceCharacters.Construction.Schemes.multiplicativeGroup_pullbackIso f)
  let c := CharacterBaseChange.Construction.Slices.presheafHomWhiskerMap (Over.map f) (yonedaGrp.obj G)
    (yonedaGrp.obj (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S))
  have hc := EvaluationBaseChange.Construction.CharacterEvaluation.value_congr a b U (c.app (Opposite.op U) χ) x
  have hw := EvaluationBaseChange.Construction.CharacterEvaluation.value_whisker (Over.map f) (yonedaGrp.obj G)
    (yonedaGrp.obj (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S)) U χ ((CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f G U).symm x)
  exact hc.trans (congrArg (EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange f U) hw)

/-- The native base-change map is the actual character comparison
after applying the size equivalences. -/
theorem EvaluationBaseChange.Construction.Schemes.nativeCharacterBaseChange_character_group {S T : Scheme.{u}} (f : T ⟶ S) (G : Grp (Over S))
    (U : (Over T)ᵒᵖ) (χ : (CharacterGroupSheaf.Construction.Schemes.nativeCharacterCommGroupPresheaf S G).obj ((Over.map f).op.obj U)) :
    CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv T ((Over.pullback f).mapGrp.obj G) U
      ((CharacterGroupOf.Construction.Schemes.nativeCharacterBaseChangeCommGroupPresheafIso f G).hom.app U χ) =
        (CharacterGroupOf.Construction.Schemes.characterBaseChangeCommGroupPresheafIso f G).hom.app U
          (CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv S G ((Over.map f).op.obj U) χ) :=
  (CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv T ((Over.pullback f).mapGrp.obj G) U).apply_symm_apply _

/-- Forgetting the group upgrade gives the original character map. -/
theorem EvaluationBaseChange.Construction.Schemes.characterBaseChangeCommGroup_apply {S T : Scheme.{u}} (f : T ⟶ S) (G : Grp (Over S))
    (U : (Over T)ᵒᵖ) (χ : (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj ((Over.map f).op.obj U)) :
    (CharacterGroupOf.Construction.Schemes.characterBaseChangeCommGroupPresheafIso f G).hom.app U χ =
      (CharacterBaseChange.Construction.Schemes.characterBaseChangePresheafIso f G).hom.app U χ := rfl

/-- The native character comparison agrees with the actual internal Hom comparison. -/
theorem EvaluationBaseChange.Construction.Schemes.nativeCharacterBaseChange_character {S T : Scheme.{u}} (f : T ⟶ S) (G : Grp (Over S))
    (U : (Over T)ᵒᵖ) (χ : (CharacterGroupSheaf.Construction.Schemes.nativeCharacterCommGroupPresheaf S G).obj ((Over.map f).op.obj U)) :
    CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv T ((Over.pullback f).mapGrp.obj G) U
      ((CharacterGroupOf.Construction.Schemes.nativeCharacterBaseChangeCommGroupPresheafIso f G).hom.app U χ) =
        (CharacterBaseChange.Construction.Schemes.characterBaseChangePresheafIso f G).hom.app U
          (CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv S G ((Over.map f).op.obj U) χ) :=
  (EvaluationBaseChange.Construction.Schemes.nativeCharacterBaseChange_character_group f G U χ).trans
    (EvaluationBaseChange.Construction.Schemes.characterBaseChangeCommGroup_apply f G U _)

/-- The point map of the pullback representative is the composite of
the pullback adjunction, the original point map, and character base change. -/
def GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.nativePointSection {S : Scheme.{u}} {G : Grp (Over S)}
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (U : Over S) (d : U ⟶ D.dual.X) :
    (CharacterGroupSheaf.Construction.Schemes.nativeCharacterCommGroupPresheaf S G).obj (Opposite.op U) :=
  D.pointsIso.hom.app (Opposite.op U) d

/-- Passing from a native point section to the actual character uses
the fixed size equivalence. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.sectionEquiv_nativePointSection {S : Scheme.{u}}
    {G : Grp (Over S)} (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (U : Over S) (d : U ⟶ D.dual.X) :
    D.sectionEquiv U d = CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv S G (Opposite.op U)
      (D.nativePointSection U d) := rfl

/-- The original representing point corresponding to a point of the
native pullback, through the pullback adjunction. -/
def GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.baseChangeOriginalPoint {S T : Scheme.{u}} {G : Grp (Over S)}
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (f : T ⟶ S) (U : Over T)
    (d : U ⟶ (D.baseChange f).dual.X) : (Over.map f).obj U ⟶ D.dual.X :=
  (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f D.dual U).symm d

/-- Native point sections of the pullback use the native character comparison. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.baseChange_points {S T : Scheme.{u}} {G : Grp (Over S)}
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (f : T ⟶ S) (U : Over T)
    (d : U ⟶ (D.baseChange f).dual.X) :
    (D.baseChange f).nativePointSection U d =
      (CharacterGroupOf.Construction.Schemes.nativeCharacterBaseChangeCommGroupPresheafIso f G).hom.app (Opposite.op U)
        (D.nativePointSection ((Over.map f).obj U)
          (D.baseChangeOriginalPoint f U d)) := rfl

/-- A native point-section formula determines its actual character. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.sectionEquiv_eq_of_nativePointSection {S : Scheme.{u}}
    {G : Grp (Over S)} (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (U : Over S) (d : U ⟶ D.dual.X)
    (χ : (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op U))
    (h : D.nativePointSection U d = (CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv S G (Opposite.op U)).symm χ) :
    D.sectionEquiv U d = χ := by
  have he := congrArg (CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv S G (Opposite.op U)) h
  exact (D.sectionEquiv_nativePointSection U d).trans
    (he.trans ((CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv S G (Opposite.op U)).apply_symm_apply χ))

/-- The native point-section formula of the pullback representative,
before applying the size equivalence. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.baseChange_nativePointSection {S T : Scheme.{u}} {G : Grp (Over S)}
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (f : T ⟶ S) (U : Over T)
    (d : U ⟶ (D.baseChange f).dual.X) :
    (D.baseChange f).nativePointSection U d =
      (CharacterGroupSheaf.Construction.Schemes.nativeCharacterSectionsMulEquiv T ((Over.pullback f).mapGrp.obj G) (Opposite.op U)).symm
        ((CharacterBaseChange.Construction.Schemes.characterBaseChangePresheafIso f G).hom.app (Opposite.op U)
          (D.sectionEquiv ((Over.map f).obj U) (D.baseChangeOriginalPoint f U d))) := rfl

/-- Sections of the native pullback represent the base changes of the
original actual character sections. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.baseChange_section {S T : Scheme.{u}} {G : Grp (Over S)}
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (f : T ⟶ S) (U : Over T)
    (d : U ⟶ (D.baseChange f).dual.X) :
    (D.baseChange f).sectionEquiv U d =
      (CharacterBaseChange.Construction.Schemes.characterBaseChangePresheafIso f G).hom.app (Opposite.op U)
        (D.sectionEquiv ((Over.map f).obj U) (D.baseChangeOriginalPoint f U d)) :=
  (D.baseChange f).sectionEquiv_eq_of_nativePointSection U d _ (D.baseChange_nativePointSection f U d)

/-- The pullback representative has the pullback evaluation pairing. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.baseChange_evaluation {S T : Scheme.{u}}
    {G : Grp (Over S)} (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (f : T ⟶ S) (U : Over T)
    (d : U ⟶ (D.baseChange f).dual.X) (x : U ⟶ ((Over.pullback f).mapGrp.obj G).X) :
    (D.baseChange f).evaluationValue U d x = EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange f U
      (D.evaluationValue ((Over.map f).obj U)
        ((CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f D.dual U).symm d) ((CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f G U).symm x)) :=
  ((D.baseChange f).evaluationValue_of_section_eq U d x (D.baseChange_section f U d)).trans
    (EvaluationBaseChange.Construction.Schemes.characterBaseChange_value f G U _ x)

/-- The canonical bidual map has the defining transposed pairing on
every test scheme. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.bidualEvaluation_pairing {S : Scheme.{u}}
    {G : Grp (Over S)} (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G)
    (E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S D.dual) (U : Over S)
    (x : U ⟶ G.X) (d : U ⟶ D.dual.X) :
    E.evaluationValue U (x ≫ (D.bidualEvaluation E).hom.hom) d = D.evaluationValue U d x := by
  have h := E.evaluationValue_of_section_eq U _ d (D.bidualEvaluation_character E U x)
  exact h.trans (congrArg (D.evaluationValue U d) (Category.id_comp x))

/-- A group morphism satisfying the transposed pairing identity is
the canonical bidual map. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.bidualEvaluation_eq_of_pairing {S : Scheme.{u}}
    {G : Grp (Over S)} (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G)
    (E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S D.dual) (c : G ⟶ E.dual)
    (h : ∀ (U : Over S) (x : U ⟶ G.X) (d : U ⟶ D.dual.X),
      E.evaluationValue U (x ≫ c.hom.hom) d = D.evaluationValue U d x) :
    D.bidualEvaluation E = c := by
  have hchar (U : Over S) (x : U ⟶ G.X) :
      E.sectionEquiv U (x ≫ c.hom.hom) = D.evaluationCharacter U x := by
    apply NatTrans.ext
    funext V
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro d
    exact (E.sectionEquiv_app U (x ≫ c.hom.hom) V.unop d).trans
      ((congrArg (fun k => E.evaluationValue V.unop.left k d)
        (Category.assoc V.unop.hom x c.hom.hom).symm).trans
          (h V.unop.left (V.unop.hom ≫ x) d))
  apply Grp.hom_ext
  have he := (E.sectionEquiv G.X).injective
    ((D.bidualEvaluation_character E G.X (𝟙 G.X)).trans (hchar G.X (𝟙 G.X)).symm)
  exact (Category.id_comp (D.bidualEvaluation E).hom.hom).symm.trans
    (he.trans (Category.id_comp c.hom.hom))

/-- Pullback of points commutes with composing a native group morphism. -/
theorem EvaluationBaseChange.Construction.Schemes.pullbackPointMulEquiv_symm_comp {S T : Scheme.{u}} (f : T ⟶ S)
    {G H : Grp (Over S)} (c : G ⟶ H) (U : Over T)
    (x : U ⟶ ((Over.pullback f).mapGrp.obj G).X) :
    (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f H U).symm (x ≫ ((Over.pullback f).mapGrp.map c).hom.hom) =
      (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f G U).symm x ≫ c.hom.hom :=
  (Over.mapPullbackAdj f).homEquiv_naturality_right_symm x c.hom.hom

/-- Canonical bidual evaluation commutes with every scheme base change. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.bidualEvaluation_baseChange {S T : Scheme.{u}}
    {G : Grp (Over S)} (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G)
    (E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S D.dual) (f : T ⟶ S) :
    (D.baseChange f).bidualEvaluation (E.baseChange f) =
      (Over.pullback f).mapGrp.map (D.bidualEvaluation E) := by
  apply (D.baseChange f).bidualEvaluation_eq_of_pairing (E.baseChange f)
  intro U x d
  let x' : (Over.map f).obj U ⟶ G.X := (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f G U).symm x
  let d' : (Over.map f).obj U ⟶ D.dual.X := (CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv f D.dual U).symm d
  have hp := EvaluationBaseChange.Construction.Schemes.pullbackPointMulEquiv_symm_comp f (D.bidualEvaluation E) U x
  have he := E.baseChange_evaluation f U
    (x ≫ ((Over.pullback f).mapGrp.map (D.bidualEvaluation E)).hom.hom) d
  have hm := congrArg (fun y => EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange f U
    (E.evaluationValue ((Over.map f).obj U) y d')) hp
  have hb := congrArg (EvaluationBaseChange.Construction.Schemes.multiplicativeGroupPointBaseChange f U)
    (D.bidualEvaluation_pairing E ((Over.map f).obj U) x' d')
  exact he.trans (hm.trans (hb.trans (D.baseChange_evaluation f U d x).symm))

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality
