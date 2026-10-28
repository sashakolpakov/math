import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Evaluation
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.GroupMap

/-! # Bidual Criterion Eq -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality

noncomputable section

/-!
# CartierDuality: identifying bidual evaluation through affine pairings
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u v w

namespace BidualCriterionEq.Construction.BidualCriterion

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- A natural pointwise pairing defines a morphism between represented presheaves. -/
def pairingPointMap (X Y Z : C)
    (b : ∀ T : C, (T ⟶ X) → (T ⟶ Y) → (T ⟶ Z))
    (hb : ∀ {T U : C} (f : U ⟶ T) (x : T ⟶ X) (y : T ⟶ Y),
      b U (f ≫ x) (f ≫ y) = f ≫ b T x y) :
    uliftYoneda.{w}.obj (X ⊗ Y) ⟶ uliftYoneda.{w}.obj Z where
  app T := ↾(fun p => ULift.up (b T.unop (p.down ≫ fst X Y) (p.down ≫ snd X Y)))
  naturality := by
    intro T U f
    apply ConcreteCategory.hom_ext
    rintro ⟨p⟩
    apply ULift.ext
    change b U.unop ((f.unop ≫ p) ≫ fst X Y) ((f.unop ≫ p) ≫ snd X Y) =
      f.unop ≫ b T.unop (p ≫ fst X Y) (p ≫ snd X Y)
    simp only [Category.assoc]
    exact hb f.unop _ _

/-- Equality of represented pairing maps gives equality on every pair of points. -/
theorem pairingPointMap_eq (X Y Z : C)
    (a b : ∀ T : C, (T ⟶ X) → (T ⟶ Y) → (T ⟶ Z))
    (ha : ∀ {T U : C} (f : U ⟶ T) (x : T ⟶ X) (y : T ⟶ Y),
      a U (f ≫ x) (f ≫ y) = f ≫ a T x y)
    (hb : ∀ {T U : C} (f : U ⟶ T) (x : T ⟶ X) (y : T ⟶ Y),
      b U (f ≫ x) (f ≫ y) = f ≫ b T x y)
    (h : pairingPointMap.{u, v, w} X Y Z a ha = pairingPointMap X Y Z b hb)
    (T : C) (x : T ⟶ X) (y : T ⟶ Y) : a T x y = b T x y := by
  have hp := congrArg
    (fun k : uliftYoneda.{w}.obj (X ⊗ Y) ⟶ uliftYoneda.{w}.obj Z =>
      (k.app (Opposite.op T) (ULift.up (lift x y))).down) h
  change a T (lift x y ≫ fst X Y) (lift x y ≫ snd X Y) =
    b T (lift x y ≫ fst X Y) (lift x y ≫ snd X Y) at hp
  rw [lift_fst, lift_snd] at hp
  exact hp

end BidualCriterionEq.Construction.BidualCriterion

/-- Equality of character sections gives equality of their values,
without unfolding the chosen group representative. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.evaluationValue_of_section_eq
    {S : Scheme.{u}} {G : Grp (Over S)} (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G)
    (T : Over S) (d : T ⟶ D.dual.X) (x : T ⟶ G.X)
    {χ : (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op T)} (h : D.sectionEquiv T d = χ) :
    D.evaluationValue T d x = Evaluation.Construction.CharacterEvaluation.value χ x :=
  congrArg (fun ψ : (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op T) => Evaluation.Construction.CharacterEvaluation.value ψ x) h

/-- Two natural pairings between represented sheaves over an affine
base agree if they agree on all affine test schemes. -/
theorem BidualCriterionEq.Construction.Schemes.pairing_eq_of_affine (R : CommRingCat.{u}) (X Y Z : Over (Spec R))
    (a b : ∀ T : Over (Spec R), (T ⟶ X) → (T ⟶ Y) → (T ⟶ Z))
    (ha : ∀ {T U : Over (Spec R)} (f : U ⟶ T) (x : T ⟶ X) (y : T ⟶ Y),
      a U (f ≫ x) (f ≫ y) = f ≫ a T x y)
    (hb : ∀ {T U : Over (Spec R)} (f : U ⟶ T) (x : T ⟶ X) (y : T ⟶ Y),
      b U (f ≫ x) (f ≫ y) = f ≫ b T x y)
    (h : ∀ (B : CommAlgCat R) (x : (algSpec R).obj (Opposite.op B) ⟶ X)
        (y : (algSpec R).obj (Opposite.op B) ⟶ Y),
      a ((algSpec R).obj (Opposite.op B)) x y = b ((algSpec R).obj (Opposite.op B)) x y)
    (T : Over (Spec R)) (x : T ⟶ X) (y : T ⟶ Y) : a T x y = b T x y := by
  let lhs : CharacterFunctor.Construction.Schemes.pointSheaf (Spec R) (X ⊗ Y) ⟶ CharacterFunctor.Construction.Schemes.pointSheaf (Spec R) Z :=
    ⟨BidualCriterionEq.Construction.BidualCriterion.pairingPointMap X Y Z a ha⟩
  let rhs : CharacterFunctor.Construction.Schemes.pointSheaf (Spec R) (X ⊗ Y) ⟶ CharacterFunctor.Construction.Schemes.pointSheaf (Spec R) Z :=
    ⟨BidualCriterionEq.Construction.BidualCriterion.pairingPointMap X Y Z b hb⟩
  have he : lhs = rhs := by
    apply (SheafDescent.Construction.affineSheafHomEquiv R _ _).injective
    apply NatTrans.ext
    funext B
    apply ConcreteCategory.hom_ext
    rintro ⟨p⟩
    apply ULift.ext
    exact h B.unop.unop (p ≫ fst X Y) (p ≫ snd X Y)
  exact BidualCriterionEq.Construction.BidualCriterion.pairingPointMap_eq X Y Z a b ha hb (congrArg (fun k => k.hom) he) T x y

/-- A character section evaluated on a further test object is the
pairing with the restricted representing point. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.sectionEquiv_app {S : Scheme.{u}} {G : Grp (Over S)}
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S G) (T : Over S) (x : T ⟶ D.dual.X)
    (U : Over T) (d : U.left ⟶ G.X) :
    (D.sectionEquiv T x).app (Opposite.op U) d = D.evaluationValue U.left (U.hom ≫ x) d := by
  obtain ⟨V, f, rfl⟩ := U.mk_surjective
  have h := congrArg
    (fun χ : (CharacterSheaf.Construction.Schemes.characterSheaf S G).obj.obj (Opposite.op V) => Evaluation.Construction.CharacterEvaluation.value χ d)
      (D.sectionEquiv_natural f x)
  exact (h.trans (Evaluation.Construction.CharacterEvaluation.value_restrict (F := yonedaGrp.obj G)
    (K := yonedaGrp.obj (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver S)) f (D.sectionEquiv T x) d)).symm

/-- A candidate bidual map is the canonical evaluation map if its
pairing formula holds on every affine test scheme. -/
theorem GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation.bidualEvaluation_eq_of_affine_pairing
    (R : CommRingCat.{u}) (G : Grp (Over (Spec R)))
    (D : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec R) G)
    (E : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec R) D.dual) (c : G ⟶ E.dual)
    (h : ∀ (B : CommAlgCat R) (x : (algSpec R).obj (Opposite.op B) ⟶ G.X)
        (d : (algSpec R).obj (Opposite.op B) ⟶ D.dual.X),
      E.evaluationValue ((algSpec R).obj (Opposite.op B)) (x ≫ c.hom.hom) d =
        D.evaluationValue ((algSpec R).obj (Opposite.op B)) d x) :
    D.bidualEvaluation E = c := by
  have ha : ∀ {T U : Over (Spec R)} (f : U ⟶ T) (x : T ⟶ G.X) (d : T ⟶ D.dual.X),
      E.evaluationValue U ((f ≫ x) ≫ c.hom.hom) (f ≫ d) =
        f ≫ E.evaluationValue T (x ≫ c.hom.hom) d := by
    intro T U f x d
    exact (congrArg (fun k => E.evaluationValue U k (f ≫ d))
      (Category.assoc f x c.hom.hom)).trans (E.evaluationValue_natural f (x ≫ c.hom.hom) d)
  have hall := BidualCriterionEq.Construction.Schemes.pairing_eq_of_affine R G.X D.dual.X (CharacterSheaf.Construction.Schemes.multiplicativeGroupOver (Spec R)).X
    (fun T x d => E.evaluationValue T (x ≫ c.hom.hom) d)
    (fun T x d => D.evaluationValue T d x) ha
    (fun f x d => D.evaluationValue_natural f d x) h
  have hchar (T : Over (Spec R)) (x : T ⟶ G.X) :
      E.sectionEquiv T (x ≫ c.hom.hom) = D.evaluationCharacter T x := by
    apply NatTrans.ext
    funext U
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro d
    exact (E.sectionEquiv_app T (x ≫ c.hom.hom) U.unop d).trans
      ((congrArg (fun k => E.evaluationValue U.unop.left k d)
        (Category.assoc U.unop.hom x c.hom.hom).symm).trans
          (hall U.unop.left (U.unop.hom ≫ x) d))
  apply Grp.hom_ext
  have he := (E.sectionEquiv G.X).injective
    ((D.bidualEvaluation_character E G.X (𝟙 G.X)).trans (hchar G.X (𝟙 G.X)).symm)
  exact (Category.id_comp (D.bidualEvaluation E).hom.hom).symm.trans
    (he.trans (Category.id_comp c.hom.hom))

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality
