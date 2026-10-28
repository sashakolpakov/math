import OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyFiniteProducts
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-! # Nonempty Cech Nerve -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve

noncomputable section

/-! The actual Čech tuple nerve requires only nonempty products, so it exists on the bounded crystalline site. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v w t z

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C] {ι : Type w} (F : ι → C)

def nerve : SimplicialObject (FormalCoproduct.{w} C) where
  obj n := (FormalCoproduct.mk ι F).power (Fin (n.unop.len + 1))
  map f := (FormalCoproduct.mk ι F).mapPower f.unop.toOrderHom.toFun
  map_id n := FormalCoproduct.mapPower_id (FormalCoproduct.mk ι F) (Fin (n.unop.len + 1))
  map_comp f g := FormalCoproduct.mapPower_comp (FormalCoproduct.mk ι F)
    g.unop.toOrderHom.toFun f.unop.toOrderHom.toFun

def complexFunctor {A : Type t} [Category.{z} A] [Preadditive A] [HasProducts.{w} A] :
    (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ :=
  FormalCoproduct.cochainComplexFunctor (nerve F)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve
