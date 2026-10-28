import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleTotal

/-! # Reindex Single -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexSingle

noncomputable section

/-! Inverse image of an ordered cover preserves the original
single-degree coordinates, including their total-complex sign. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {C D : Type u} [Preorder C] [HasFiniteProducts C] [Preorder D] [HasFiniteProducts D]
  (r : C ⥤ D) [PreservesFiniteLimits r]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {A : Type v} [Category A] [Abelian A] [HasProducts.{u} A] [HasCoproducts.{0} A]
  (P : Dᵒᵖ ⥤ A) (c g : ℕ)

theorem comparison :
    homologyMap (ReindexTotal.totalIso r U
      ((single (Dᵒᵖ ⥤ A) (.up ℕ) c).obj P)).hom (g+c) ≫
      (Functor.SingleTotal.homologyIso (Functor.Projection.functor (r.obj ∘ U)) P c g).hom =
    (Functor.SingleTotal.homologyIso
      (ReindexTotal.restriction r ⋙ Functor.Projection.functor U) P c g).hom ≫
      homologyMap (Reindex.iso r U P).hom g :=
  Functor.SingleTotal.homology_naturality P c (Reindex.functorIso r U).hom g

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexSingle
