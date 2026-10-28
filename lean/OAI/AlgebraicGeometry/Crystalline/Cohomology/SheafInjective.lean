import Mathlib.CategoryTheory.Generator.Sheaf
import Mathlib.CategoryTheory.Limits.MonoCoprod
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! # Sheaf Injective -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjective.SheafInjectiveRestrictions

noncomputable section

/-!
# Restriction along monomorphisms for injective sheaves

Free representable presheaves carry monomorphisms of site objects to
monomorphisms. Left exact sheafification preserves these maps. Injectivity
then extends maps from any coefficient object across the restriction.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe v u v' u'

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasCoproducts.{v} A]

def presheafMap {P Q : C} (f : P ⟶ Q) (M : A) :
    Presheaf.freeYoneda P M ⟶ Presheaf.freeYoneda Q M where
  app Y := Sigma.map' (fun (g : Y.unop ⟶ P) => g ≫ f) (fun _ => 𝟙 M)
  naturality _ _ _ := by
    apply Sigma.hom_ext
    intro g
    simp [Presheaf.freeYoneda, Category.assoc]

instance presheafMap_mono [HasZeroMorphisms A] {P Q : C} (f : P ⟶ Q) [Mono f] (M : A) :
    Mono (presheafMap f M) := by
  have : ∀ Y, Mono ((presheafMap f M).app Y) := by
    intro Y
    exact MonoCoprod.mono_map'_of_injective (fun (_ : Y.unop ⟶ Q) => M)
      (fun (g : Y.unop ⟶ P) => g ≫ f) (fun _ _ h => (cancel_mono f).mp h)
  exact NatTrans.mono_of_mono_app _

theorem presheafHomEquiv_map {P Q : C} (f : P ⟶ Q) (M : A)
    {F : Cᵒᵖ ⥤ A} (α : Presheaf.freeYoneda Q M ⟶ F) :
    Presheaf.freeYonedaHomEquiv (presheafMap f M ≫ α) =
      Presheaf.freeYonedaHomEquiv α ≫ F.map f.op := by
  have hm : Sigma.ι (fun (_ : P ⟶ P) => M) (𝟙 P) ≫ (presheafMap f M).app (op P) =
      Sigma.ι (fun (_ : P ⟶ Q) => M) f := by
    change Sigma.ι (fun (_ : P ⟶ P) => M) (𝟙 P) ≫
      Sigma.map' (f := fun (_ : P ⟶ Q) => M) (fun (g : P ⟶ P) => g ≫ f) (fun _ => 𝟙 M) = _
    simp
  have hr : Sigma.ι (fun (_ : Q ⟶ Q) => M) (𝟙 Q) ≫
      (Presheaf.freeYoneda Q M).map f.op = Sigma.ι (fun (_ : P ⟶ Q) => M) f := by
    change Sigma.ι (fun (_ : Q ⟶ Q) => M) (𝟙 Q) ≫
      Sigma.map' (f := fun (_ : P ⟶ Q) => M) (fun (g : Q ⟶ Q) => f ≫ g) (fun _ => 𝟙 M) = _
    simp
  have h := congrArg (fun g => Sigma.ι (fun (_ : Q ⟶ Q) => M) (𝟙 Q) ≫ g)
    (α.naturality f.op)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ α.app (op P)) hm).trans
      ((congrArg (fun g => g ≫ α.app (op P)) hr).symm.trans
        ((Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm))))

variable (J : GrothendieckTopology C) [HasWeakSheafify J A]

def sheafMap {P Q : C} (f : P ⟶ Q) (M : A) :
    Sheaf.freeYoneda J P M ⟶ Sheaf.freeYoneda J Q M :=
  (presheafToSheaf J A).map (presheafMap f M)

instance sheafMap_mono [HasZeroMorphisms A]
    [(presheafToSheaf J A).PreservesMonomorphisms]
    {P Q : C} (f : P ⟶ Q) [Mono f] (M : A) : Mono (sheafMap J f M) := by
  dsimp [sheafMap]
  have : Mono (presheafMap f M) := presheafMap_mono f M
  exact Functor.PreservesMonomorphisms.preserves (F := presheafToSheaf J A) (presheafMap f M)

theorem sheafHomEquiv_map {P Q : C} (f : P ⟶ Q) (M : A)
    {F : Sheaf J A} (α : Sheaf.freeYoneda J Q M ⟶ F) :
    Sheaf.freeYonedaHomEquiv (sheafMap J f M ≫ α) =
      Sheaf.freeYonedaHomEquiv α ≫ F.obj.map f.op := by
  change Presheaf.freeYonedaHomEquiv
    ((sheafificationAdjunction J A).homEquiv _ _ ((presheafToSheaf J A).map (presheafMap f M) ≫ α)) = _
  have h := (sheafificationAdjunction J A).homEquiv_naturality_left (presheafMap f M) α
  exact (congrArg Presheaf.freeYonedaHomEquiv h).trans (presheafHomEquiv_map f M _)

theorem exists_extension [HasZeroMorphisms A]
    [(presheafToSheaf J A).PreservesMonomorphisms]
    {P Q : C} (f : P ⟶ Q) [Mono f] (M : A)
    (I : Sheaf J A) [Injective I] (a : M ⟶ I.obj.obj (op P)) :
    ∃ b : M ⟶ I.obj.obj (op Q), b ≫ I.obj.map f.op = a := by
  let α : Sheaf.freeYoneda J P M ⟶ I := Sheaf.freeYonedaHomEquiv.symm a
  let β := Injective.factorThru α (sheafMap J f M)
  refine ⟨Sheaf.freeYonedaHomEquiv β, ?_⟩
  rw [← sheafHomEquiv_map J f M β, Injective.comp_factorThru]
  exact Sheaf.freeYonedaHomEquiv.apply_symm_apply a

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.SheafInjective.SheafInjectiveRestrictions
