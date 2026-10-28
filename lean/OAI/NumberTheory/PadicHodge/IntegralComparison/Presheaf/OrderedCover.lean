import OAI.NumberTheory.PadicHodge.IntegralComparison.OrderedCech.EdgeRefinement

/-! # Ordered Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.OrderedCover.Comparison

noncomputable section

/-! Common-cover comparison and its coefficient naturality for genuine
presheaf complexes. The formulas are the original ordered refinements,
with no module-linearity requirement on a coefficient-complex map. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {X : TopCat.{u}}
  {D : Type v} [Category D] [Abelian D] [HasProducts.{u} D] [HasCoproducts.{0} D]
  {ι κ ν : Type u} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (U : ι → Opens X) (V : κ → Opens X) (W : ν → Opens X)
  (r : FormalCoproduct.mk ν W ⟶ FormalCoproduct.mk ι U)
  (s : FormalCoproduct.mk ν W ⟶ FormalCoproduct.mk κ V)

def totalFunctor : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ ⥤ CochainComplex D ℕ :=
  (OrderedCech.Functor.Projection.functor U).mapHomologicalComplex (.up ℕ) ⋙
    HomologicalComplex₂.totalFunctor D (.up ℕ) (.up ℕ) (.up ℕ)

def refinement : Comparison.totalFunctor (D := D) U ⟶ Comparison.totalFunctor W :=
  Functor.whiskerRight
    (NatTrans.mapHomologicalComplex (OrderedCech.Refinement.transformation U W r) (.up ℕ))
    (HomologicalComplex₂.totalFunctor D (.up ℕ) (.up ℕ) (.up ℕ))

theorem total_naturality {K L : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ} (a : K ⟶ L) :
    (Comparison.totalFunctor U).map a ≫ OrderedCech.Refinement.totalMap U W r L =
      OrderedCech.Refinement.totalMap U W r K ≫ (Comparison.totalFunctor W).map a :=
  (refinement U W r).naturality a

theorem homology_naturality {K L : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ}
    (a : K ⟶ L) (q : ℕ) :
    homologyMap ((Comparison.totalFunctor U).map a) q ≫
        homologyMap (OrderedCech.Refinement.totalMap U W r L) q =
      homologyMap (OrderedCech.Refinement.totalMap U W r K) q ≫
        homologyMap ((Comparison.totalFunctor W).map a) q := by
  simpa only [homologyMap_comp] using
    congrArg (fun f => homologyMap f q) (total_naturality U W r a)

def comparison (K : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ) (q : ℕ)
    [IsIso (homologyMap (OrderedCech.Refinement.totalMap V W s K) q)] :=
  homologyMap (OrderedCech.Refinement.totalMap U W r K) q ≫
    inv (homologyMap (OrderedCech.Refinement.totalMap V W s K) q)

theorem naturality {K L : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ}
    (a : K ⟶ L) (q : ℕ)
    [IsIso (homologyMap (OrderedCech.Refinement.totalMap V W s K) q)]
    [IsIso (homologyMap (OrderedCech.Refinement.totalMap V W s L) q)] :
    homologyMap ((Comparison.totalFunctor U).map a) q ≫ comparison U V W r s L q =
      comparison U V W r s K q ≫ homologyMap ((Comparison.totalFunctor V).map a) q := by
  apply (cancel_mono (homologyMap (OrderedCech.Refinement.totalMap V W s L) q)).mp
  simp only [comparison, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [homology_naturality V W s a q, IsIso.inv_hom_id_assoc]
  exact homology_naturality U W r a q

theorem edge (K : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ) (q : ℕ)
    [IsIso (homologyMap (OrderedCech.Refinement.totalMap V W s K) q)] :
    homologyMap (OrderedCechEdge.edge U K) q ≫ comparison U V W r s K q =
      homologyMap (OrderedCechEdge.edge V K) q := by
  apply (cancel_mono (homologyMap (OrderedCech.Refinement.totalMap V W s K) q)).mp
  simp only [comparison, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact (OrderedCech.EdgeRefinement.homology U W r K q).trans
    (OrderedCech.EdgeRefinement.homology V W s K q).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.OrderedCover.Comparison
