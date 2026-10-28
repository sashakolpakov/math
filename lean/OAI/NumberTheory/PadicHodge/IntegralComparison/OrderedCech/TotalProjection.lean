import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.Refinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Functor.SingleTotal
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-! # Total Projection -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.TotalProjection

noncomputable section

/-! The original ordinary-to-ordered Čech projection is natural for
complexes and preserves the original single-degree homology comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {D : Type v} [Category D] [Abelian D] [HasProducts.{u} D] [HasCoproducts.{0} D]
  {ι : Type u} [LinearOrder ι] (U : ι → C)

local instance ordinary_additive : (NonemptyCechNerve.complexFunctor U (A := D)).Additive := by
  change (FormalCoproduct.cochainComplexFunctor (NonemptyCechNerve.nerve U)).Additive
  infer_instance

abbrev ordinary : CochainComplex (Cᵒᵖ ⥤ D) ℕ ⥤ CochainComplex D ℕ :=
  (NonemptyCechNerve.complexFunctor U).mapHomologicalComplex (.up ℕ) ⋙
    HomologicalComplex₂.totalFunctor D (.up ℕ) (.up ℕ) (.up ℕ)

abbrev ordered : CochainComplex (Cᵒᵖ ⥤ D) ℕ ⥤ CochainComplex D ℕ :=
  (Functor.Projection.functor U).mapHomologicalComplex (.up ℕ) ⋙
    HomologicalComplex₂.totalFunctor D (.up ℕ) (.up ℕ) (.up ℕ)

def bicomplexMap (K : CochainComplex (Cᵒᵖ ⥤ D) ℕ) :=
  (NatTrans.mapHomologicalComplex (Naturality.projectionTransformation U) (.up ℕ)).app K

def map (K : CochainComplex (Cᵒᵖ ⥤ D) ℕ) : (ordinary U).obj K ⟶ (ordered U).obj K :=
  HomologicalComplex₂.total.map (bicomplexMap U K) (.up ℕ)

theorem naturality {K L : CochainComplex (Cᵒᵖ ⥤ D) ℕ} (a : K ⟶ L) :
    (ordinary U).map a ≫ TotalProjection.map U L = TotalProjection.map U K ≫ (ordered U).map a := by
  let T := HomologicalComplex₂.totalFunctor D (.up ℕ) (.up ℕ) (.up ℕ)
  exact (T.map_comp _ _).symm.trans
    ((congrArg T.map ((NatTrans.mapHomologicalComplex
      (Naturality.projectionTransformation U) (.up ℕ)).naturality a)).trans (T.map_comp _ _))

theorem homology_naturality {K L : CochainComplex (Cᵒᵖ ⥤ D) ℕ} (a : K ⟶ L) (n : ℕ) :
    homologyMap ((ordinary U).map a) n ≫ homologyMap (TotalProjection.map U L) n =
      homologyMap (TotalProjection.map U K) n ≫ homologyMap ((ordered U).map a) n := by
  exact (homologyMap_comp _ _ n).symm.trans
    ((congrArg (fun b => homologyMap b n) (TotalProjection.naturality U a)).trans (homologyMap_comp _ _ n))

theorem single (P : Cᵒᵖ ⥤ D) (c n : ℕ) :
    homologyMap (TotalProjection.map U ((HomologicalComplex.single _ (.up ℕ) c).obj P)) (n+c) ≫
      (Functor.SingleTotal.homologyIso (Functor.Projection.functor U) P c n).hom =
    (Functor.SingleTotal.homologyIso (NonemptyCechNerve.complexFunctor U) P c n).hom ≫
      homologyMap (Projection.map U P) n :=
  Functor.SingleTotal.homology_naturality P c (Naturality.projectionTransformation U) n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.TotalProjection
