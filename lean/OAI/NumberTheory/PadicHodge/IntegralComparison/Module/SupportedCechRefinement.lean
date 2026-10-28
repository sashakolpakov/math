import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechRefinementTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCech

/-! # Supported Cech Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SupportedCechRefinement

noncomputable section

/-! Supported refinement preserves the actual module-valued edge with
independent space, index and coefficient universes. Exact rows make the
refinement an isomorphism on homology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCechEdge

private theorem iso_of_triangle {D : Type*} [Category D] {A B C : D}
    (a : A ⟶ B) (b : A ⟶ C) (f : B ⟶ C) [IsIso a] [IsIso b]
    (h : a ≫ f = b) : IsIso f := by
  have hf : f = inv a ≫ b := by
    apply (cancel_epi a).mp
    simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using h
  rw [hf]
  infer_instance

universe u v w z
variable (R : Type u) [CommRing R] (X : TopCat.{v})
  {C : Type w} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Opens X) {ι κ : Type w} [LinearOrder ι] [LinearOrder κ]
  (U : ι → C) (V : κ → C)
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)
  (O : Opens X)
  (K : CochainComplex (Sheaf (Opens.grothendieckTopology X)
    (ModuleCat.{max u v w z} R)) ℕ)
  (hU : ∀ i, F.obj (U i) ≤ O) (hV : ∀ i, F.obj (V i) ≤ O)

local instance coefficient_limits [UnivLE.{w,z}] : HasLimitsOfSize.{w,w} (ModuleCat.{z} R) :=
  ModuleCat.hasLimitsOfSize.{w,w,z,u}
local instance coefficient_colimits : HasColimitsOfSize.{0,0} (ModuleCat.{z} R) :=
  ModuleCat.hasColimitsOfSize.{z,u,0,0} R

theorem component (q : ℕ) :
    Supported.OrderedCechEdge.component.{u,v,w,z} R X F U O K q ≫
      ((AugmentedOrdered.CechRefinementTotal.bicomplexMap U V r
        (Supported.OrderedCechEdge.presheafComplex.{u,v,w,z} R X F K)).f q).f 0 =
      Supported.OrderedCechEdge.component.{u,v,w,z} R X F V O K q := by
  change (_ ≫ (AugmentedOrdered.CechZero.zeroIso U (F.op ⋙ (K.X q).obj)).inv) ≫
      (AugmentedOrdered.CechRefinement.map U V r (F.op ⋙ (K.X q).obj)).f 0 = _
  rw [AugmentedOrdered.CechRefinement.map_f_zero]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

theorem edge : Supported.OrderedCechEdge.map.{u,v,w,z} R X F U O K hU ≫
    AugmentedOrdered.CechRefinementTotal.totalMap U V r (Supported.OrderedCechEdge.presheafComplex.{u,v,w,z} R X F K) =
      Supported.OrderedCechEdge.map.{u,v,w,z} R X F V O K hV := by
  apply HomologicalComplex.Hom.ext
  funext q
  simp only [Supported.OrderedCechEdge.map, HomologicalComplex.comp_f,
    AlgebraicGeometry.SheafCohomology.Cech.UpNatHorizontalEdge.HomologicalComplex₂.totalUpNatHorizontalEdge_f,
    AugmentedOrdered.CechRefinementTotal.totalMap, Category.assoc,
    HomologicalComplex₂.ιTotal_map]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun a => a ≫ (Supported.OrderedCechEdge.bicomplex.{u,v,w,z} R X F V K).ιTotal (.up ℕ) q 0 q rfl)
      (component.{u,v,w,z} R X F U V r O K q))

theorem homology_edge (q : ℕ) :
    homologyMap (Supported.OrderedCechEdge.map.{u,v,w,z} R X F U O K hU) q ≫
      homologyMap (AugmentedOrdered.CechRefinementTotal.totalMap U V r
        (Supported.OrderedCechEdge.presheafComplex.{u,v,w,z} R X F K)) q =
      homologyMap (Supported.OrderedCechEdge.map.{u,v,w,z} R X F V O K hV) q := by
  simpa only [homologyMap_comp] using
    congrArg (fun a => homologyMap a q) (edge.{u,v,w,z} R X F U V r O K hU hV)

include hU hV in
theorem isIso
    (hcU : F.obj (⊤_ C) ⊓ O ≤ ⨆ i, F.obj (U i))
    (hcV : F.obj (⊤_ C) ⊓ O ≤ ⨆ i, F.obj (V i))
    (hrU : ∀ q r, ((Supported.OrderedCechEdge.bicomplex.{u,v,w,z} R X F U K).X q).ExactAt (r+1))
    (hrV : ∀ q r, ((Supported.OrderedCechEdge.bicomplex.{u,v,w,z} R X F V K).X q).ExactAt (r+1)) (q : ℕ) :
    IsIso (homologyMap (AugmentedOrdered.CechRefinementTotal.totalMap U V r
      (Supported.OrderedCechEdge.presheafComplex.{u,v,w,z} R X F K)) q) := by
  let := Supported.OrderedCech.Comparison.quasiIso.{u,v,w,z} R X F U O K hU hcU hrU
  let := Supported.OrderedCech.Comparison.quasiIso.{u,v,w,z} R X F V O K hV hcV hrV
  exact iso_of_triangle _ _ _ (homology_edge.{u,v,w,z} R X F U V r O K hU hV q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SupportedCechRefinement
