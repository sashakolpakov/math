import OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.OrderedCoverRefinement
import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CechTransferCoordinates

/-! # Ordered Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.OrderedCover.Comparison

noncomputable section

/-! Actual common affine refinements compare ordered additive totals
and retain the original resolution transfer. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.OrderedCoverRefinement
variable {X : Scheme.{u}} [X.IsSeparated]
  {ι κ ν : Type u} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  (U : ι → X.Opens) (V : κ → X.Opens) (W : ν → X.Opens)
  (r : FormalCoproduct.mk ν W ⟶ FormalCoproduct.mk ι U)
  (s : FormalCoproduct.mk ν W ⟶ FormalCoproduct.mk κ V)
  (hU : iSup U = ⊤) (hV : iSup V = ⊤) (hW : iSup W = ⊤)
  (haU : ∀ i, IsAffineOpen (U i)) (haV : ∀ i, IsAffineOpen (V i))
  (haW : ∀ i, IsAffineOpen (W i))

def iso (K : CochainComplex X.Modules ℕ) [∀ q, (K.X q).IsQuasicoherent] (q : ℕ) := by
  letI := OrderedCoverRefinement.homology_isIso U W r hU hW haU haW K q
  letI := OrderedCoverRefinement.homology_isIso V W s hV hW haV haW K q
  exact asIso (OrderedCoverRefinement.homology U W r K q) ≪≫ (asIso (OrderedCoverRefinement.homology V W s K q)).symm

variable {P K T : CochainComplex X.Modules ℕ}
  [∀ q, (P.X q).IsQuasicoherent] [∀ q, (K.X q).IsQuasicoherent]
  [∀ q, (T.X q).IsQuasicoherent]

theorem naturality (a : P ⟶ K) (q : ℕ) :
    (OrderedCechConcentration.functor U q).map a ≫
      (iso U V W r s hU hV hW haU haV haW K q).hom =
    (iso U V W r s hU hV hW haU haV haW P q).hom ≫
      (OrderedCechConcentration.functor V q).map a := by
  let := OrderedCoverRefinement.homology_isIso V W s hV hW haV haW K q
  let := OrderedCoverRefinement.homology_isIso V W s hV hW haV haW P q
  apply (cancel_mono (OrderedCoverRefinement.homology V W s K q)).mp
  simp only [iso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [OrderedCoverRefinement.homology_naturality V W s a q, IsIso.inv_hom_id_assoc]
  exact OrderedCoverRefinement.homology_naturality U W r a q

variable (l : K ⟶ T) [QuasiIso l] (a : P ⟶ T) (q : ℕ)

theorem transfer :
    IntrinsicOrdered.CechTransferCoordinates.Intrinsic.genericMap (𝟙 X) U haU q l a ≫
      (iso U V W r s hU hV hW haU haV haW K q).hom =
    (iso U V W r s hU hV hW haU haV haW P q).hom ≫
      IntrinsicOrdered.CechTransferCoordinates.Intrinsic.genericMap (𝟙 X) V haV q l a := by
  let := IntrinsicOrdered.CechTransferCoordinates.Intrinsic.generic_left_isIso (𝟙 X) U haU q l
  let := IntrinsicOrdered.CechTransferCoordinates.Intrinsic.generic_left_isIso (𝟙 X) V haV q l
  apply (cancel_mono ((OrderedCechConcentration.functor V q).map l)).mp
  have hl := naturality U V W r s hU hV hW haU haV haW l q
  have ha := naturality U V W r s hU hV hW haU haV haW a q
  change (((OrderedCechConcentration.functor U q).map a ≫
    inv ((OrderedCechConcentration.functor U q).map l)) ≫
      (iso U V W r s hU hV hW haU haV haW K q).hom) ≫
        (OrderedCechConcentration.functor V q).map l =
    ((iso U V W r s hU hV hW haU haV haW P q).hom ≫
      ((OrderedCechConcentration.functor V q).map a ≫
        inv ((OrderedCechConcentration.functor V q).map l))) ≫
          (OrderedCechConcentration.functor V q).map l
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← hl, IsIso.inv_hom_id_assoc]
  exact ha

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.OrderedCover.Comparison
