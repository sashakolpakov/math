import OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjective
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Sites.Abelian

/-! # Yoneda Add Equiv -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Free.YonedaAddEquiv.FreeYonedaAddEquiv

noncomputable section

/-!
# Additive section equivalences for free representables

The free representable Yoneda equivalence is additive, as is the
sheafification adjunction. Morphisms from a coproduct are additively
equivalent to families of morphisms from its summands. These equivalences
provide the degreewise duality between free Čech chains and section cochains.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v u' v' w

section Coproduct

variable {A : Type u'} [Category.{v'} A] [Preadditive A]
  {ι : Type w} (P : ι → A) [HasCoproduct P] (Y : A)

def coproduct : ((∐ P) ⟶ Y) ≃+ (∀ i, P i ⟶ Y) where
  toFun f i := Sigma.ι P i ≫ f
  invFun f := Sigma.desc f
  left_inv f := Sigma.hom_ext _ _ (fun i => Sigma.ι_comp_desc (fun j => Sigma.ι P j ≫ f) i)
  right_inv f := funext (fun i => Sigma.ι_comp_desc f i)
  map_add' f g := funext (fun i => Preadditive.comp_add _ _ _ (Sigma.ι P i) f g)

end Coproduct

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [Abelian A] [HasCoproducts.{v} A]

def presheaf (P : C) (M : A) (F : Cᵒᵖ ⥤ A) :
    (Presheaf.freeYoneda P M ⟶ F) ≃+ (M ⟶ F.obj (op P)) where
  toEquiv := Presheaf.freeYonedaHomEquiv
  map_add' f g := by
    change Sigma.ι (fun (_ : P ⟶ P) => M) (𝟙 P) ≫ (f.app (op P) + g.app (op P)) = _
    exact Preadditive.comp_add _ _ _ _ _ _

variable (J : GrothendieckTopology C) [HasSheafify J A]

def sheaf (P : C) (M : A) (F : Sheaf J A) :
    (Sheaf.freeYoneda J P M ⟶ F) ≃+ (M ⟶ F.obj.obj (op P)) :=
  ((sheafificationAdjunction J A).homAddEquiv (Presheaf.freeYoneda P M) F).trans
    (presheaf P M F.obj)

theorem sheaf_apply (P : C) (M : A) (F : Sheaf J A) (f : Sheaf.freeYoneda J P M ⟶ F) :
    sheaf J P M F f = Sheaf.freeYonedaHomEquiv f := rfl

theorem sheaf_natural_left {P Q : C} (f : P ⟶ Q) (M : A) (F : Sheaf J A)
    (a : Sheaf.freeYoneda J Q M ⟶ F) :
    sheaf J P M F (SheafInjective.SheafInjectiveRestrictions.sheafMap J f M ≫ a) =
      sheaf J Q M F a ≫ F.obj.map f.op :=
  SheafInjective.SheafInjectiveRestrictions.sheafHomEquiv_map J f M a

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Free.YonedaAddEquiv.FreeYonedaAddEquiv
