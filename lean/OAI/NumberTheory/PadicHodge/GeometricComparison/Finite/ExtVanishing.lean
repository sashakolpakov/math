import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Algebra.Category.Grp.Zero

/-! # Ext Vanishing -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.ExtVanishing.FiniteExtVanishing

noncomputable section

/-! Finite products and coproducts preserve coefficient Ext vanishing. -/

open _root_.CategoryTheory Abelian Limits Opposite

universe u v w z

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  (A : C) {ι : Type z} [Finite ι] (F : ι → C) (n : ℕ)

theorem product [HasProduct F] (hF : ∀ i, Subsingleton (Ext.{w} A (F i) n)) :
    Subsingleton (Ext.{w} A (∏ᶜ F) n) := by
  let H := (extFunctor.{w} n : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat.{w}).obj (op A)
  have : H.Additive := inferInstanceAs (extFunctorObj A n).Additive
  have hzero (i : ι) : IsZero (H.obj (F i)) := by
    have : Subsingleton (H.obj (F i)) := hF i
    exact AddCommGrpCat.isZero_of_subsingleton _
  have hprod : IsZero (∏ᶜ fun i => H.obj (F i)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply Pi.hom_ext
    intro i
    exact (hzero i).eq_of_tgt _ _
  exact AddCommGrpCat.subsingleton_of_isZero (hprod.of_iso (PreservesProduct.iso H F))

theorem coproduct [HasCoproduct F] (hF : ∀ i, Subsingleton (Ext.{w} A (F i) n)) :
    Subsingleton (Ext.{w} A (∐ F) n) := by
  let H := (extFunctor.{w} n : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat.{w}).obj (op A)
  have : H.Additive := inferInstanceAs (extFunctorObj A n).Additive
  have hzero (i : ι) : IsZero (H.obj (F i)) := by
    have : Subsingleton (H.obj (F i)) := hF i
    exact AddCommGrpCat.isZero_of_subsingleton _
  have hsum : IsZero (∐ fun i => H.obj (F i)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply Sigma.hom_ext
    intro i
    exact (hzero i).eq_of_src _ _
  exact AddCommGrpCat.subsingleton_of_isZero (hsum.of_iso (PreservesCoproduct.iso H F))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.ExtVanishing.FiniteExtVanishing
