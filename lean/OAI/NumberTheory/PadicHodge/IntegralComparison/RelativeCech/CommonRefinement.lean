import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.Refinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.CechRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.SupportedRecovery

/-! # Common Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.CommonRefinement

noncomputable section

/-! A common refinement compares the local residue cover with a
global complementary cover and recovers the original supported class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private theorem recovery_eq {D : Type*} [Category D] {A B C E T : D}
    (a : A ⟶ B) (b : A ⟶ C) (r : B ⟶ E) (s : C ⟶ E) [IsIso s]
    (e : C ⟶ T) (h : a ≫ r = b ≫ s) :
    a ≫ r ≫ inv s ≫ e = b ≫ e := by
  rw [← Category.assoc a, h]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]

universe u
variable {X : TopCat.{u}} (U : Opens X)
  {ι κ ν : Type u} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (V : ι → Opens X) (W : κ → Opens X) (T : ν → Opens X)
  (r : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk ι V)
  (s : FormalCoproduct.mk ν T ⟶ FormalCoproduct.mk κ W)
  {D : Type (u+1)} [Category.{u} D] [Abelian D] [HasLimitsOfSize.{u,u} D]
  [HasCoproducts.{0} D]
  (K : CochainComplex ((Opens X)ᵒᵖ ⥤ D) ℕ) (n : ℕ)

def comparison [IsIso (Refinement.homology U W T s K n)] :
    ((Total.source U V K).total (.up ℕ)).homology n ⟶
      ((Total.target U W K).total (.up ℕ)).homology n :=
  Refinement.homology U V T r K n ≫
    inv (Refinement.homology U W T s K n) ≫
      homologyMap (Total.map U W K) n

omit K in
theorem supported_recovery
    (O : Opens X) (L : CochainComplex (Sheaf (Opens.grothendieckTopology X) D) ℕ)
    (hzero : ∀ q, IsZero ((L.X q).obj.obj (Opposite.op O)))
    (hV : ∀ i, V i ≤ O) (hW : ∀ i, W i ≤ O) (hT : ∀ i, T i ≤ O)
    [IsIso (Refinement.homology U W T s
      (SupportedCoordinates.underlying D X L) n)] :
    homologyMap (SupportedRecovery.localLift D X U V O L hzero hV) n ≫
      comparison U V W T r s (SupportedCoordinates.underlying D X L) n =
        homologyMap (Presheaf.OrderedCechEdge.edge
          (Intersections.cover U W)
          (SupportedCoordinates.underlying D X L)) n := by
  have hr := congrArg (fun a => homologyMap a n)
    (Supported.CechRefinement.global_lift D X (Intersections.intersect U)
      V T r O L (fun i => inf_le_right.trans (hV i))
      (fun i => inf_le_right.trans (hT i)) hzero)
  have hs := congrArg (fun a => homologyMap a n)
    (Supported.CechRefinement.global_lift D X (Intersections.intersect U)
      W T s O L (fun i => inf_le_right.trans (hW i))
      (fun i => inf_le_right.trans (hT i)) hzero)
  simp only [homologyMap_comp, Category.assoc] at hr hs
  have h : homologyMap (SupportedRecovery.localLift D X U V O L hzero hV) n ≫
      Refinement.homology U V T r
        (SupportedCoordinates.underlying D X L) n =
    homologyMap (SupportedRecovery.localLift D X U W O L hzero hW) n ≫
      Refinement.homology U W T s
        (SupportedCoordinates.underlying D X L) n := by
    simp only [SupportedRecovery.localLift, homologyMap_comp, Category.assoc]
    convert hr.trans hs.symm using 1 <;> rfl
  unfold comparison
  rw [recovery_eq _ _ _ _ _ h]
  exact SupportedRecovery.homology_recovery D X U W O L hzero hW n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.CommonRefinement
