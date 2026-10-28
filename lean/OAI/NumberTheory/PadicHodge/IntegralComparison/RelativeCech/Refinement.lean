import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Total
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechRefinementTotal

/-! # Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Refinement

noncomputable section

/-! Refinement of the complementary opens is natural on the actual
relative Čech totals and their cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v
variable {X : TopCat.{u}} (U : Opens X)
  {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  (V : ι → Opens X) (W : κ → Opens X)
  (r : FormalCoproduct.mk κ W ⟶ FormalCoproduct.mk ι V)
  {D : Type v} [Category D] [Abelian D] [HasProducts.{u} D] [HasCoproducts.{0} D]

abbrev restriction : ((Opens X)ᵒᵖ ⥤ D) ⥤ (Opens X)ᵒᵖ ⥤ D :=
  (Functor.whiskeringLeft _ _ _).obj (Intersections.intersect U).op

def map (K : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ) :
    (Total.source U V K).total (.up ℕ) ⟶
      (Total.source U W K).total (.up ℕ) :=
  AugmentedOrdered.CechRefinementTotal.totalMap V W r
    (((restriction U).mapHomologicalComplex (.up ℕ)).obj K)

theorem naturality {K L : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ} (a : K ⟶ L) :
    Total.sourceMap U V a ≫ Refinement.map U V W r L =
      Refinement.map U V W r K ≫ Total.sourceMap U W a := by
  let T := HomologicalComplex₂.totalFunctor D (.up ℕ) (.up ℕ) (.up ℕ)
  have h := (NatTrans.mapHomologicalComplex
    (AugmentedOrdered.CechRefinementTotal.transformation V W r (D := D)) (.up ℕ)).naturality
      (((restriction U).mapHomologicalComplex (.up ℕ)).map a)
  exact (T.map_comp _ _).symm.trans ((congrArg T.map h).trans (T.map_comp _ _))

def homology (K : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ) (n : ℕ) :=
  homologyMap (Refinement.map U V W r K) n

theorem homology_naturality {K L : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ}
    (a : K ⟶ L) (n : ℕ) :
    homologyMap (Total.sourceMap U V a) n ≫ homology U V W r L n =
      homology U V W r K n ≫ homologyMap (Total.sourceMap U W a) n := by
  simpa only [homology, homologyMap_comp] using
    congrArg (fun f => homologyMap f n) (Refinement.naturality U V W r a)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Refinement
