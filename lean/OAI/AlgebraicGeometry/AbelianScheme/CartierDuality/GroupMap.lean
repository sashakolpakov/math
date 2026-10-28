import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterGroupSheaf
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafDescent

/-! # Group Map -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.GroupMap

noncomputable section

/-!
# CartierDuality: checking character-group morphisms on affine tests
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u v w

namespace Construction

namespace GroupMapDescent

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

omit [CartesianMonoidalCategory C] in
/-- Naturality of a map out of the lifted Yoneda presheaf, written
directly on ordinary morphisms of the test category. -/
theorem pointMap_naturality (F : Cᵒᵖ ⥤ Type (max v w)) (X : C)
    (a : uliftYoneda.{w}.obj X ⟶ F) {T U : Cᵒᵖ} (f : T ⟶ U) (g : T.unop ⟶ X) :
    a.app U (ULift.up (f.unop ≫ g)) = F.map f (a.app T (ULift.up g)) :=
  congrArg
    (fun k : (uliftYoneda.{w}.obj X).obj T ⟶ F.obj U => k (ULift.up g)) (a.naturality f)

/-- Multiply the images of the two projections under a represented
presheaf map with commutative-group-valued target. -/
def pairedMap (F : Cᵒᵖ ⥤ CommGrpCat.{max v w}) (X : C)
    (a : uliftYoneda.{w}.obj X ⟶ F ⋙ forget CommGrpCat) :
    uliftYoneda.{w}.obj (X ⊗ X) ⟶ F ⋙ forget CommGrpCat where
  app T := ↾(fun p => a.app T (ULift.up (p.down ≫ fst X X)) *
    a.app T (ULift.up (p.down ≫ snd X X)))
  naturality := by
    intro T U f
    apply ConcreteCategory.hom_ext
    rintro ⟨p⟩
    have h₁ : a.app U (ULift.up (f.unop ≫ p ≫ fst X X)) =
        F.map f (a.app T (ULift.up (p ≫ fst X X))) :=
      pointMap_naturality (F ⋙ forget CommGrpCat) X a f (p ≫ fst X X)
    have h₂ : a.app U (ULift.up (f.unop ≫ p ≫ snd X X)) =
        F.map f (a.app T (ULift.up (p ≫ snd X X))) :=
      pointMap_naturality (F ⋙ forget CommGrpCat) X a f (p ≫ snd X X)
    change a.app U (ULift.up ((f.unop ≫ p) ≫ fst X X)) *
        a.app U (ULift.up ((f.unop ≫ p) ≫ snd X X)) =
      F.map f (a.app T (ULift.up (p ≫ fst X X)) * a.app T (ULift.up (p ≫ snd X X)))
    simp only [Category.assoc]
    exact (congrArg₂ (fun x y : F.obj U => x * y) h₁ h₂).trans
      ((F.map f).hom.map_mul _ _).symm

/-- Multiplication after a map to the product is the product of its two coordinates. -/
theorem comp_multiplication {X T : C} [MonObj X] (p : T ⟶ X ⊗ X) :
    p ≫ μ[X] = (p ≫ fst X X) * (p ≫ snd X X) := by
  rw [Hom.mul_def, lift_comp_fst_snd]

/-- Equality of the two product maps proves preservation of multiplication
on every test object. -/
theorem map_mul_of_pair_eq (F : Cᵒᵖ ⥤ CommGrpCat.{max v w}) (X : C) [MonObj X]
    (a : uliftYoneda.{w}.obj X ⟶ F ⋙ forget CommGrpCat)
    (h : uliftYoneda.map μ[X] ≫ a = pairedMap F X a)
    (T : C) (f g : T ⟶ X) :
    a.app (Opposite.op T) (ULift.up (f * g)) =
      a.app (Opposite.op T) (ULift.up f) * a.app (Opposite.op T) (ULift.up g) := by
  have hp := congrArg
    (fun b : uliftYoneda.{w}.obj (X ⊗ X) ⟶ F ⋙ forget CommGrpCat =>
      b.app (Opposite.op T) (ULift.up (lift f g))) h
  change a.app (Opposite.op T) (ULift.up (lift f g ≫ μ[X])) =
    a.app (Opposite.op T) (ULift.up (lift f g ≫ fst X X)) *
      a.app (Opposite.op T) (ULift.up (lift f g ≫ snd X X)) at hp
  rw [lift_fst, lift_snd] at hp
  exact hp

end GroupMapDescent

namespace Schemes

/-- A sheaf map from a represented group to characters is multiplicative
as soon as it is multiplicative on all affine test schemes. -/
theorem characterMap_mul_of_affine (R : CommRingCat.{u}) (G : Grp (Over (Spec R)))
    (X : Over (Spec R)) [MonObj X]
    (a : CharacterFunctor.Construction.Schemes.pointSheaf (Spec R) X ⟶ CharacterSheaf.Construction.Schemes.characterSheaf (Spec R) G)
    (h : ∀ (B : CommAlgCat R) (f g : (algSpec R).obj (Opposite.op B) ⟶ X),
      a.hom.app (Opposite.op ((algSpec R).obj (Opposite.op B))) (ULift.up (f * g)) =
        a.hom.app (Opposite.op ((algSpec R).obj (Opposite.op B))) (ULift.up f) *
          a.hom.app (Opposite.op ((algSpec R).obj (Opposite.op B))) (ULift.up g))
    (T : Over (Spec R)) (f g : T ⟶ X) :
    a.hom.app (Opposite.op T) (ULift.up (f * g)) =
      a.hom.app (Opposite.op T) (ULift.up f) * a.hom.app (Opposite.op T) (ULift.up g) := by
  let F := CharacterGroupSheaf.Construction.Schemes.characterCommGroupPresheaf (Spec R) G
  let lhs : CharacterFunctor.Construction.Schemes.pointSheaf (Spec R) (X ⊗ X) ⟶ CharacterSheaf.Construction.Schemes.characterSheaf (Spec R) G :=
    ⟨uliftYoneda.map μ[X] ≫ a.hom⟩
  let rhs : CharacterFunctor.Construction.Schemes.pointSheaf (Spec R) (X ⊗ X) ⟶ CharacterSheaf.Construction.Schemes.characterSheaf (Spec R) G :=
    ⟨GroupMapDescent.pairedMap F X a.hom⟩
  have he : lhs = rhs := by
    apply (SheafDescent.Construction.affineSheafHomEquiv R _ _).injective
    apply NatTrans.ext
    funext B
    apply ConcreteCategory.hom_ext
    rintro ⟨p⟩
    change a.hom.app (Opposite.op ((algSpec R).obj B.unop)) (ULift.up (p ≫ μ[X])) =
      a.hom.app (Opposite.op ((algSpec R).obj B.unop)) (ULift.up (p ≫ fst X X)) *
        a.hom.app (Opposite.op ((algSpec R).obj B.unop)) (ULift.up (p ≫ snd X X))
    exact (congrArg
      (fun k => a.hom.app (Opposite.op ((algSpec R).obj B.unop)) (ULift.up k))
        (GroupMapDescent.comp_multiplication p)).trans (h B.unop.unop _ _)
  exact GroupMapDescent.map_mul_of_pair_eq F X a.hom (congrArg (fun k => k.hom) he) T f g

end Schemes

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.GroupMap
