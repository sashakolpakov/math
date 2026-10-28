import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.ConstantSubpresheaf

/-! # Injective Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.InjectiveSections

noncomputable section

/-!
# IntegralComparison: injective presheaves extend sections from incoming-closed full subcategories
-/

open _root_.CategoryTheory Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.ConstantSubpresheaf

universe u v w

variable {C : Type u} [Category.{v} C] (R : Type w) [Ring R] (M : ModuleCat.{w} R)
  (P : ObjectProperty C) (hP : ∀ {U V : C}, (U ⟶ V) → P V → P U)
  (F : Cᵒᵖ ⥤ ModuleCat.{w} R) [Injective F]

def extend (a : (Functor.const P.FullSubcategoryᵒᵖ).obj M ⟶ P.ι.op ⋙ F) : (Functor.const Cᵒᵖ).obj M ⟶ F :=
  Injective.factorThru (ConstantSubpresheaf.lift R M P hP F a) (ConstantSubpresheaf.inclusion R M P hP)

theorem restrict_extend (a : (Functor.const P.FullSubcategoryᵒᵖ).obj M ⟶ P.ι.op ⋙ F) :
    Functor.whiskerLeft P.ι.op (extend R M P hP F a) = a := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  classical
  let y : ConstantSubpresheaf.support R M P U.unop.obj := ⟨x, by simp only [ConstantSubpresheaf.support, ite_eq_left U.unop.property, Submodule.mem_top]⟩
  have h := congrArg (fun t : ConstantSubpresheaf.presheaf R M P hP ⟶ F => t.app (op U.unop.obj) y)
    (Injective.comp_factorThru (ConstantSubpresheaf.lift R M P hP F a) (ConstantSubpresheaf.inclusion R M P hP))
  exact h.trans (ConstantSubpresheaf.liftMap_inside R M P F a U.unop.obj U.unop.property y)

include hP in
theorem restriction_surjective : Function.Surjective
    (fun a : (Functor.const Cᵒᵖ).obj M ⟶ F => Functor.whiskerLeft P.ι.op a) :=
  fun a => ⟨extend R M P hP F a, restrict_extend R M P hP F a⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.InjectiveSections
