import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.RefinementTransfer
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.CommonRefinement

/-! # Transfer Common -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.TransferCommon.Comparison

noncomputable section

/-! Common-cover extension commutes with the original derived
right/inverse-left map, including canonical concentration maps. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private theorem square {C : Type*} [Category C]
    {A B D E F G H I : C} (a : A ⟶ B) (b : D ⟶ E) (c : F ⟶ G) (d : H ⟶ I)
    (r : A ⟶ D) (r' : B ⟶ E) (s : F ⟶ D) (s' : G ⟶ E)
    (t : F ⟶ H) (t' : G ⟶ I) [IsIso s] [IsIso s']
    (hr : a ≫ r' = r ≫ b) (hs : c ≫ s' = s ≫ b) (ht : c ≫ t' = t ≫ d) :
    a ≫ (r' ≫ inv s' ≫ t') = (r ≫ inv s ≫ t) ≫ d := by
  have hi : b ≫ inv s' = inv s ≫ c := by
    simpa only [Category.assoc, IsIso.inv_hom_id_assoc, IsIso.hom_inv_id,
      Category.comp_id] using congrArg (fun f => inv s ≫ f ≫ inv s') hs.symm
  calc
    _ = (a ≫ r') ≫ inv s' ≫ t' := by simp only [Category.assoc]
    _ = (r ≫ b) ≫ inv s' ≫ t' := by rw [hr]
    _ = r ≫ (b ≫ inv s') ≫ t' := by simp only [Category.assoc]
    _ = r ≫ (inv s ≫ c) ≫ t' := by rw [hi]
    _ = _ := by simp only [Category.assoc]; rw [ht]

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCech.RefinementTransfer
variable {X : Scheme.{u}} [X.IsSeparated] (U : X.Opens) (hU : IsAffineOpen U)
  {ι κ ν : Type u} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (V : ι → X.Opens) (hV : ∀ i, IsAffineOpen (V i))
  (W : κ → X.Opens) (hW : ∀ i, IsAffineOpen (W i))
  (J : ν → X.Opens) (hJ : ∀ i, IsAffineOpen (J i))
  (r : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk ι V)
  (s : FormalCoproduct.mk ν J ⟶ FormalCoproduct.mk κ W)
  {P K T : CochainComplex X.Modules ℕ}
  [∀ q, (K.X q).IsQuasicoherent] [∀ q, (T.X q).IsQuasicoherent]
  (l : K ⟶ T) [QuasiIso l] (a : P ⟶ T) (q : ℕ)
  [IsIso (RelativeCech.Refinement.homology U W J s (AdditiveCechConcentration.coefficients K) q)]
  [IsIso (RelativeCech.Refinement.homology U W J s (AdditiveCechConcentration.coefficients P) q)]

include hJ in
theorem comparison : RelativeCech.RefinementTransfer.map U hU V hV q l a ≫
    RelativeCech.CommonRefinement.comparison U V W J r s (AdditiveCechConcentration.coefficients K) q =
  RelativeCech.CommonRefinement.comparison U V W J r s (AdditiveCechConcentration.coefficients P) q ≫
    RelativeCech.RefinementTransfer.globalMap U hU W hW q l a :=
  square (RelativeCech.RefinementTransfer.map U hU V hV q l a) (RelativeCech.RefinementTransfer.map U hU J hJ q l a) (RelativeCech.RefinementTransfer.map U hU W hW q l a)
    (RelativeCech.RefinementTransfer.globalMap U hU W hW q l a) _ _ _ _ _ _
    (RelativeCech.RefinementTransfer.refinement_square U hU V hV J hJ r q l a)
    (RelativeCech.RefinementTransfer.refinement_square U hU W hW J hJ s q l a)
    (RelativeCech.RefinementTransfer.extension_square U hU W hW q l a)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.TransferCommon.Comparison
