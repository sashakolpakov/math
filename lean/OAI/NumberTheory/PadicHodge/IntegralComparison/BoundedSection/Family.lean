import OAI.NumberTheory.PadicHodge.IntegralComparison.CountableProductHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.AllBoundedSectionsFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.ComplexExact

/-! # Family -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.Family

noncomputable section

/-!
# IntegralComparison: all bounded section complexes as a countable family
-/

open _root_.CategoryTheory

open OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustivePresheafSections

universe u v

variable {C : Type u} [Category.{v} C] (R : Type u) [CommRing R]
  (P : ℕ → ObjectProperty C) (M : ModuleCat.{u} R)

def functor : (Cᵒᵖ ⥤ ModuleCat.{u} R) ⥤ (Discrete ℕ ⥤ ModuleCat.{u} R) where
  obj F := Discrete.functor (fun n => ModuleCat.of R (ExhaustivePresheafSections.Stage P M F n))
  map β := Discrete.natTrans (fun n => ModuleCat.ofHom (Linear.rightComp R _ (Functor.whiskerLeft (P n.as).ι.op β)))
  map_id F := by
    apply NatTrans.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact Category.comp_id a
  map_comp α β := by
    apply NatTrans.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (Category.assoc a (Functor.whiskerLeft (P n.as).ι.op α) (Functor.whiskerLeft (P n.as).ι.op β)).symm

instance additive : (Family.functor R P M).Additive where
  map_add {F G} α β := by
    apply NatTrans.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact Preadditive.comp_add _ _ _ a (Functor.whiskerLeft (P n.as).ι.op α) (Functor.whiskerLeft (P n.as).ι.op β)

def productIso : Family.functor R P M ⋙ CountableModuleProduct.functor R ≅
    AllBoundedSectionsFunctor.functor R P M := Iso.refl _

def complex (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ) :
    CochainComplex (Discrete ℕ ⥤ ModuleCat.{u} R) ℕ :=
  ((Family.functor R P M).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

def productComplexIso (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ) :
    CountableProductHomology.complex R (complex R P M K) ≅
      ComplexExact.allComplex R P M K := Iso.refl _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.Family
