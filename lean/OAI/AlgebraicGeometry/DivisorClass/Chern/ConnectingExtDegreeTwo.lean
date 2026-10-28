import OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingResolutionDegreeTwo
import OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingExt

/-! # Connecting Ext Degree Two -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingExtDegreeTwo

noncomputable section

/-! The actual Yoneda product with an extension is the constructed degree-two resolution class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive _root_.CategoryTheory.Abelian
open _root_.CochainComplex.HomComplex DerivedCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w w'
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  [HasDerivedCategory.{w'} C] {S : ShortComplex C} (hS : S.ShortExact)
  {Y : C} (R : InjectiveResolution Y) (f : S.X₁ ⟶ R.cocomplex.X 1)
  (hf : f ≫ R.cocomplex.d 1 2 = 0)

theorem resolutionOneCocycle_extMk_hom :
    (R.extMk f 2 rfl hf).hom =
      ShiftedHom.comp (ShiftedHom.map (Cocycle.equivHomShift.symm (ConnectingResolutionDegreeTwo.resolutionOneCocycle R f hf)) Q)
        (ShiftedHom.mk₀ (0 : ℤ) rfl (inv (Q.map R.ι'))) (zero_add 1) := by
  rw [R.extMk_hom]
  simp only [singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    ShiftedHom.comp_mk₀]
  erw [ShiftedHom.mk₀_id_comp, Category.comp_id]
  rfl

theorem connectingResolutionTwoCocycle_extMk_hom :
    (R.extMk (ConnectingResolutionDegreeTwo.connectingResolutionTwoQuotient hS R f hf) 3 rfl
      (ConnectingResolutionDegreeTwo.connectingResolutionTwoQuotient_closed hS R f hf)).hom =
      ShiftedHom.comp
        (ShiftedHom.map (Cocycle.equivHomShift.symm (ConnectingResolutionDegreeTwo.connectingResolutionTwoCocycle hS R f hf)) Q)
        (ShiftedHom.mk₀ (0 : ℤ) rfl (inv (Q.map R.ι'))) (zero_add 2) := by
  rw [R.extMk_hom]
  simp only [singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    ShiftedHom.comp_mk₀]
  erw [ShiftedHom.mk₀_id_comp, Category.comp_id]
  rfl

theorem connectingExtDegreeTwo_hom :
    ShiftedHom.comp hS.extClass.hom
      (ShiftedHom.map (Cocycle.equivHomShift.symm (ConnectingResolutionDegreeTwo.resolutionOneCocycle R f hf)) Q)
      (show (1 : ℤ) + 1 = 2 from rfl) =
      ShiftedHom.map (Cocycle.equivHomShift.symm (ConnectingResolutionDegreeTwo.connectingResolutionTwoCocycle hS R f hf)) Q := by
  rw [ShortComplex.ShortExact.extClass_hom, ConnectingExt.singleConnecting_eq_triangle]
  exact ConnectingDerivedDegreeTwo.connectingDerivedDegreeTwo (S.map (CochainComplex.singleFunctor C 0))
    (ConnectingResolutionDegreeTwo.resolutionOneCocycle R f hf) (ConnectingResolutionDegreeTwo.connectingResolutionOneCochain hS R f)
    (ConnectingResolutionDegreeTwo.connectingResolutionTwoCocycle hS R f hf)
    (ConnectingResolutionDegreeTwo.connectingResolutionOneCochain_lift hS R f hf) (ConnectingResolutionDegreeTwo.connectingResolutionOneCochain_d hS R f hf)
    (hS.map_of_exact (HomologicalComplex.single C (.up ℤ) 0))

theorem connectingExt_comp_resolutionOne :
    hS.extClass.comp (R.extMk f 2 rfl hf) (show 1 + 1 = 2 from rfl) =
      R.extMk (ConnectingResolutionDegreeTwo.connectingResolutionTwoQuotient hS R f hf) 3 rfl
        (ConnectingResolutionDegreeTwo.connectingResolutionTwoQuotient_closed hS R f hf) := by
  ext
  rw [Ext.comp_hom, resolutionOneCocycle_extMk_hom, connectingResolutionTwoCocycle_extMk_hom]
  let b := ShiftedHom.map (Cocycle.equivHomShift.symm (ConnectingResolutionDegreeTwo.resolutionOneCocycle R f hf)) Q
  let g := ShiftedHom.mk₀ (0 : ℤ) rfl (inv (Q.map R.ι'))
  have ha := ShiftedHom.comp_assoc hS.extClass.hom b g
    (show (1 : ℤ) + 1 = 2 from rfl) (zero_add 1) (show (0 : ℤ) + 1 + 1 = 2 from rfl)
  exact ha.symm.trans (congrArg (fun z => ShiftedHom.comp z g (zero_add 2))
    (connectingExtDegreeTwo_hom hS R f hf))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingExtDegreeTwo
