import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
import Mathlib.Algebra.Homology.Additive

/-! # Module Functor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ModuleFunctor

noncomputable section

/-! The actual principal-open section functor on module sheaves. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.SectionPresheaf
variable {X : Scheme.{u}} (U : X.Opens) (hU : IsAffineOpen U)

def functor : X.Modules ⥤ ((SectionPresheaf.Index U)ᵒᵖ ⥤ ModuleCat.{u} Γ(X, U)) where
  obj M := SectionPresheaf.modules U hU M
  map f := SectionPresheaf.moduleHom U hU f
  map_id M := by
    apply NatTrans.ext
    funext r
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext r
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl

instance additive : (functor U hU).Additive where
  map_add {M N} f g := by
    apply NatTrans.ext
    funext r
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.ModuleFunctor
