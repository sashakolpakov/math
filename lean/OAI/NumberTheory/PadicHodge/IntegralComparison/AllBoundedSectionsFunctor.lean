import OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustiveSectionNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.Difference

/-! # All Bounded Sections Functor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AllBoundedSectionsFunctor

noncomputable section

/-!
# IntegralComparison: the product of all bounded section functors and its difference transformation
-/

open _root_.CategoryTheory

open OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustivePresheafSections OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustiveLinearSections

universe u v w z t

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
  [Preadditive D] (R : Type t) [CommRing R] [Linear R D]
  (P : ℕ → ObjectProperty C) (hP : Monotone P) (M : D)

def map {F G : Cᵒᵖ ⥤ D} (β : F ⟶ G) : (∀ n, ExhaustivePresheafSections.Stage P M F n) →ₗ[R] (∀ n, ExhaustivePresheafSections.Stage P M G n) where
  toFun a n := a n ≫ Functor.whiskerLeft (P n).ι.op β
  map_add' a b := by
    funext n
    exact Preadditive.add_comp _ _ _ (a n) (b n) (Functor.whiskerLeft (P n).ι.op β)
  map_smul' r a := by
    funext n
    exact Linear.smul_comp _ _ _ r (a n) (Functor.whiskerLeft (P n).ι.op β)

def functor : (Cᵒᵖ ⥤ D) ⥤ ModuleCat.{max u z} R where
  obj F := ModuleCat.of R (∀ n, ExhaustivePresheafSections.Stage P M F n)
  map β := ModuleCat.ofHom (AllBoundedSectionsFunctor.map R P M β)
  map_id F := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    funext n
    exact Category.comp_id (a n)
  map_comp α β := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    funext n
    exact (Category.assoc (a n) (Functor.whiskerLeft (P n).ι.op α) (Functor.whiskerLeft (P n).ι.op β)).symm

instance additive : (functor R P M).Additive where
  map_add {F G} α β := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    funext n
    exact Preadditive.comp_add _ _ _ (a n) (Functor.whiskerLeft (P n).ι.op α) (Functor.whiskerLeft (P n).ι.op β)

def inclusion : ExhaustiveSectionNaturality.boundedSectionsFunctor R P hP M ⟶ functor R P M where
  app F := ModuleCat.ofHom (ExhaustiveLinearSections.compatibleSubmodule R P hP M F).subtype
  naturality _ _ _ := ModuleCat.hom_ext (LinearMap.ext (fun _ => rfl))

def difference : functor R P M ⟶ functor R P M where
  app F := ModuleCat.ofHom (BoundedSection.Difference.difference P hP M F R)
  naturality F G β := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    funext n
    change (a n ≫ Functor.whiskerLeft (P n).ι.op β) -
      (ExhaustivePresheafSections.restrict P hP M F n (n + 1) (Nat.le_succ n) (a (n + 1)) ≫ Functor.whiskerLeft (P n).ι.op β) =
        (a n - ExhaustivePresheafSections.restrict P hP M F n (n + 1) (Nat.le_succ n) (a (n + 1))) ≫ Functor.whiskerLeft (P n).ι.op β
    rw [Preadditive.sub_comp]

theorem inclusion_difference : inclusion R P hP M ≫ difference R P hP M = 0 := by
  apply NatTrans.ext
  funext F
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact (BoundedSection.Difference.compatible_iff_difference_zero P hP M F R a.val).mp a.property

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AllBoundedSectionsFunctor
