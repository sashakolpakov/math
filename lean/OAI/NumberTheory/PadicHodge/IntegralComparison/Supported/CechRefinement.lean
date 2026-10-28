import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechRefinementTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.SupportedOrderedCechEdge
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.ZeroComplementComplex

/-! # Cech Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechRefinement

noncomputable section

/-! Refining the nonempty members of a supported Čech cover preserves
the original supported-section edge and every global supported lift. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open OAI.NumberTheory.PadicHodge.IntegralComparison.SupportedOrderedCechEdge.Abelian

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (D : Type (u+1)) [Category.{u} D] [Abelian D] [HasLimitsOfSize.{u,u} D]
  [HasCoproducts.{0} D]
  (X : TopCat.{u}) {C : Type u} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Opens X) {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  (U : ι → C) (V : κ → C)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  (O : Opens X) (K : CochainComplex (Sheaf (Opens.grothendieckTopology X) D) ℕ)
  (hU : ∀ i, F.obj (U i) ≤ O) (hV : ∀ i, F.obj (V i) ≤ O)

omit [HasCoproducts D] in
theorem component (q : ℕ) :
    SupportedOrderedCechEdge.Abelian.component D X F U O K q ≫
      ((AugmentedOrdered.CechRefinementTotal.bicomplexMap U V r
        (SupportedOrderedCechEdge.Abelian.presheafComplex D X F K)).f q).f 0 =
      SupportedOrderedCechEdge.Abelian.component D X F V O K q := by
  change (_ ≫ (AugmentedOrdered.CechZero.zeroIso U (F.op ⋙ (K.X q).obj)).inv) ≫
      (AugmentedOrdered.CechRefinement.map U V r (F.op ⋙ (K.X q).obj)).f 0 = _
  rw [AugmentedOrdered.CechRefinement.map_f_zero]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

theorem edge : SupportedOrderedCechEdge.Abelian.map D X F U O K hU ≫
    AugmentedOrdered.CechRefinementTotal.totalMap U V r (SupportedOrderedCechEdge.Abelian.presheafComplex D X F K) =
      SupportedOrderedCechEdge.Abelian.map D X F V O K hV := by
  apply HomologicalComplex.Hom.ext
  funext q
  simp only [SupportedOrderedCechEdge.Abelian.map, HomologicalComplex.comp_f,
    AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge_f,
    AugmentedOrdered.CechRefinementTotal.totalMap, Category.assoc,
    HomologicalComplex₂.ιTotal_map]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun a => a ≫ (SupportedOrderedCechEdge.Abelian.bicomplex D X F V K).ιTotal (.up ℕ) q 0 q rfl)
      (component D X F U V r O K q))

theorem homology_edge (q : ℕ) :
    HomologicalComplex.homologyMap (SupportedOrderedCechEdge.Abelian.map D X F U O K hU) q ≫
      HomologicalComplex.homologyMap
        (AugmentedOrdered.CechRefinementTotal.totalMap U V r (SupportedOrderedCechEdge.Abelian.presheafComplex D X F K)) q =
      HomologicalComplex.homologyMap (SupportedOrderedCechEdge.Abelian.map D X F V O K hV) q := by
  simpa only [HomologicalComplex.homologyMap_comp] using
    congrArg (fun a => HomologicalComplex.homologyMap a q) (edge D X F U V r O K hU hV)

theorem global_lift (hzero : ∀ q, IsZero ((K.X q).obj.obj (op O))) :
    (ZeroComplementComplex.lift O (F.obj (⊤_ C)) K hzero ≫
      SupportedOrderedCechEdge.Abelian.map D X F U O K hU) ≫
        AugmentedOrdered.CechRefinementTotal.totalMap U V r (SupportedOrderedCechEdge.Abelian.presheafComplex D X F K) =
    ZeroComplementComplex.lift O (F.obj (⊤_ C)) K hzero ≫
      SupportedOrderedCechEdge.Abelian.map D X F V O K hV := by
  rw [Category.assoc, edge]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechRefinement
