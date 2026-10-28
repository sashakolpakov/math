import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.InjectiveSections
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Injective Restriction Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.InjectiveRestrictionSections

noncomputable section

/-!
# IntegralComparison: injective module sheaves extend presheaf sections from bounded subsites
-/

open _root_.CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] (R : Type w) [Ring R]
  (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{w} R)]

instance forget_preservesInjectives : (sheafToPresheaf J (ModuleCat.{w} R)).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (sheafificationAdjunction J (ModuleCat.{w} R))

variable (M : ModuleCat.{w} R) (P : ObjectProperty C)
  (hP : ∀ {U V : C}, (U ⟶ V) → P V → P U)
  (F : Sheaf J (ModuleCat.{w} R)) [Injective F]

include hP in
theorem restriction_surjective : Function.Surjective
    (fun a : (Functor.const Cᵒᵖ).obj M ⟶ F.obj => Functor.whiskerLeft P.ι.op a) := by
  let : Injective F.obj := (sheafToPresheaf J (ModuleCat.{w} R)).injective_obj F
  exact Incoming.InjectiveSections.restriction_surjective R M P hP F.obj

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.InjectiveRestrictionSections
