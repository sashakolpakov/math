import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Reindex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.TotalProjection

/-! # Reindex Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexTotal

noncomputable section

/-! Reindexing ordered Cech totals preserves coefficient maps and
the original projection from the full Cech total. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {C D : Type u} [Preorder C] [HasFiniteProducts C] [Preorder D] [HasFiniteProducts D]
  (r : C ⥤ D) [PreservesFiniteLimits r]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {A : Type v} [Category A] [Abelian A] [HasProducts.{u} A] [HasCoproducts.{0} A]

abbrev restriction : (Dᵒᵖ ⥤ A) ⥤ Cᵒᵖ ⥤ A := (Functor.whiskeringLeft _ _ _).obj r.op

variable (K : CochainComplex (Dᵒᵖ ⥤ A) ℕ)

def bicomplexIso :
    ((OrderedCech.Functor.Projection.functor U).mapHomologicalComplex (.up ℕ)).obj
      (((restriction r).mapHomologicalComplex (.up ℕ)).obj K) ≅
    ((OrderedCech.Functor.Projection.functor (r.obj ∘ U)).mapHomologicalComplex (.up ℕ)).obj K :=
  (NatIso.mapHomologicalComplex (Reindex.functorIso r U) (.up ℕ)).app K

def totalIso :
    (TotalProjection.ordered U).obj
      (((restriction r).mapHomologicalComplex (.up ℕ)).obj K) ≅
    (TotalProjection.ordered (r.obj ∘ U)).obj K :=
  HomologicalComplex₂.total.mapIso (bicomplexIso r U K) (.up ℕ)

theorem naturality {L : CochainComplex (Dᵒᵖ ⥤ A) ℕ} (a : K ⟶ L) :
    (TotalProjection.ordered U).map
      (((restriction r).mapHomologicalComplex (.up ℕ)).map a) ≫ (totalIso r U L).hom =
    (totalIso r U K).hom ≫ (TotalProjection.ordered (r.obj ∘ U)).map a := by
  let T := HomologicalComplex₂.totalFunctor A (.up ℕ) (.up ℕ) (.up ℕ)
  exact (T.map_comp _ _).symm.trans
    ((congrArg T.map ((NatIso.mapHomologicalComplex
      (Reindex.functorIso r U) (.up ℕ)).hom.naturality a)).trans (T.map_comp _ _))

theorem projection :
    (Cech.ComplexBaseChange.totalIso r U K).hom ≫
      TotalProjection.map (r.obj ∘ U) K =
    TotalProjection.map U (((restriction r).mapHomologicalComplex (.up ℕ)).obj K) ≫
      (totalIso r U K).hom := by
  have h : (Cech.ComplexBaseChange.bicomplexIso r U K).hom ≫
      TotalProjection.bicomplexMap (r.obj ∘ U) K =
    TotalProjection.bicomplexMap U
      (((restriction r).mapHomologicalComplex (.up ℕ)).obj K) ≫ (bicomplexIso r U K).hom := by
    apply HomologicalComplex.Hom.ext
    funext q
    exact Reindex.projection r U (K.X q)
  let T := HomologicalComplex₂.totalFunctor A (.up ℕ) (.up ℕ) (.up ℕ)
  exact (T.map_comp _ _).symm.trans ((congrArg T.map h).trans (T.map_comp _ _))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.ReindexTotal
