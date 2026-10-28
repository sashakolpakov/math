import OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustiveLinearSections
import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # Exhaustive Section Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustiveSectionNaturality

noncomputable section

/-!
# IntegralComparison: bounded-section reconstruction is natural in the coefficient presheaf
-/

open _root_.CategoryTheory

open OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustivePresheafSections OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustiveLinearSections

universe u v w z t

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
  [Preadditive D] (R : Type t) [CommRing R] [Linear R D]
  (P : ℕ → ObjectProperty C) (hP : Monotone P) (hC : ∀ U, ∃ n, P n U) (M : D)

def globalSectionsFunctor : (Cᵒᵖ ⥤ D) ⥤ ModuleCat.{max u z} R where
  obj F := ModuleCat.of R ((Functor.const Cᵒᵖ).obj M ⟶ F)
  map β := ModuleCat.ofHom (Linear.rightComp R _ β)
  map_id F := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact Category.comp_id a
  map_comp α β := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (Category.assoc a α β).symm

def map {F G : Cᵒᵖ ⥤ D} (β : F ⟶ G) :
    ExhaustiveLinearSections.compatibleSubmodule R P hP M F →ₗ[R] ExhaustiveLinearSections.compatibleSubmodule R P hP M G where
  toFun a := ⟨fun n => a.val n ≫ Functor.whiskerLeft (P n).ι.op β, by
    intro n m hnm
    exact congrArg (fun t => t ≫ Functor.whiskerLeft (P n).ι.op β) (a.property n m hnm)⟩
  map_add' a b := by
    apply Subtype.ext
    funext n
    exact Preadditive.add_comp _ _ _ (a.val n) (b.val n) (Functor.whiskerLeft (P n).ι.op β)
  map_smul' r a := by
    apply Subtype.ext
    funext n
    exact Linear.smul_comp _ _ _ r (a.val n) (Functor.whiskerLeft (P n).ι.op β)

def boundedSectionsFunctor : (Cᵒᵖ ⥤ D) ⥤ ModuleCat.{max u z} R where
  obj F := ModuleCat.of R (ExhaustiveLinearSections.compatibleSubmodule R P hP M F)
  map β := ModuleCat.ofHom (ExhaustiveSectionNaturality.map R P hP M β)
  map_id F := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    funext n
    exact Category.comp_id (a.val n)
  map_comp α β := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    funext n
    exact (Category.assoc (a.val n) (Functor.whiskerLeft (P n).ι.op α) (Functor.whiskerLeft (P n).ι.op β)).symm

instance globalSectionsFunctor_additive : (globalSectionsFunctor (C := C) R M).Additive where
  map_add {F G} α β := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact Preadditive.comp_add _ _ _ a α β

instance boundedSectionsFunctor_additive : (boundedSectionsFunctor R P hP M).Additive where
  map_add {F G} α β := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    funext n
    exact Preadditive.comp_add _ _ _ (a.val n) (Functor.whiskerLeft (P n).ι.op α) (Functor.whiskerLeft (P n).ι.op β)

def iso : globalSectionsFunctor (C := C) R M ≅ boundedSectionsFunctor R P hP M :=
  NatIso.ofComponents (fun F => (ExhaustiveLinearSections.linearEquiv R P hP hC M F).toModuleIso) (by
    intro F G β
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    funext n
    rfl)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustiveSectionNaturality
