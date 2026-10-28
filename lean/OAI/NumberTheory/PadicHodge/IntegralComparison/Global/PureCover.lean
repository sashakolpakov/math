import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.PureSectionClass

/-! # Pure Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Global.PureCover.Comparison

noncomputable section

/-! The canonical global class of a pure complex and its original
resolution transfer are independent of the chosen affine cover. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} [X.IsSeparated]
  {ι κ ν : Type u} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (U : ι → X.Opens) (V : κ → X.Opens) (W : ν → X.Opens)
  (r : FormalCoproduct.mk ν W ⟶ FormalCoproduct.mk ι U)
  (s : FormalCoproduct.mk ν W ⟶ FormalCoproduct.mk κ V)
  (hU : iSup U = ⊤) (hV : iSup V = ⊤) (hW : iSup W = ⊤)
  (haU : ∀ i, IsAffineOpen (U i)) (haV : ∀ i, IsAffineOpen (V i))
  (haW : ∀ i, IsAffineOpen (W i))
  (P : CochainComplex X.Modules ℕ) [∀ q, (P.X q).IsQuasicoherent]
  (c : ℕ) (hP : ∀ q, q ≠ c → P.ExactAt q) (q : ℕ)

theorem comparison : PureSectionClass.map U haU P c hP q ≫
    (Additive.OrderedCover.Comparison.iso U V W r s hU hV hW haU haV haW P q).hom =
      PureSectionClass.map V haV P c hP q := by
  let := Additive.OrderedCoverRefinement.homology_isIso V W s hV hW haV haW P q
  apply (cancel_mono (Additive.OrderedCoverRefinement.homology V W s P q)).mp
  simp only [Additive.OrderedCover.Comparison.iso, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact (PureSectionClass.refinement U haU P c hP W haW r q).trans
    (PureSectionClass.refinement V haV P c hP W haW s q).symm

variable {K T : CochainComplex X.Modules ℕ}
  [∀ q, (K.X q).IsQuasicoherent] [∀ q, (T.X q).IsQuasicoherent]
  (l : K ⟶ T) [QuasiIso l] (a : P ⟶ T)

theorem transfer :
    (PureSectionClass.map U haU P c hP q ≫
      IntrinsicOrdered.CechTransferCoordinates.Intrinsic.genericMap (𝟙 X) U haU q l a) ≫
        (Additive.OrderedCover.Comparison.iso U V W r s hU hV hW haU haV haW K q).hom =
    PureSectionClass.map V haV P c hP q ≫
      IntrinsicOrdered.CechTransferCoordinates.Intrinsic.genericMap (𝟙 X) V haV q l a := by
  rw [Category.assoc,
    Additive.OrderedCover.Comparison.transfer U V W r s hU hV hW haU haV haW l a q,
    ← Category.assoc, comparison U V W r s hU hV hW haU haV haW P c hP q]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Global.PureCover.Comparison
