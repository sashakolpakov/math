import OAI.NumberTheory.PadicHodge.IntegralComparison.LinearAdjunction
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Linear.FunctorCategory

/-! # Sheaf Linear -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafLinear

noncomputable section

/-!
# IntegralComparison: sheafification and constant module sheaves retain coefficient linearity
-/

open _root_.CategoryTheory

universe u v w z

variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{z} R)]

instance forget_linear : (sheafToPresheaf J (ModuleCat.{z} R)).Linear R where
  map_smul := by intros; rfl

instance sheafify_linear : (presheafToSheaf J (ModuleCat.{z} R)).Linear R :=
  LinearAdjunction.left_linear R (sheafificationAdjunction J (ModuleCat.{z} R))

instance constantPresheaf_linear :
    (Functor.const Cᵒᵖ : ModuleCat.{z} R ⥤ (Cᵒᵖ ⥤ ModuleCat.{z} R)).Linear R where
  map_smul := by intros; rfl

instance constant_linear : (constantSheaf J (ModuleCat.{z} R)).Linear R := by
  dsimp [constantSheaf]
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafLinear
