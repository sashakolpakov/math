import OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingResolutionCocycle
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-! # Connecting Ext -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingExt

noncomputable section

/-! Compute the actual extension class from the constructed injective-resolution cocycle. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive _root_.CategoryTheory.Abelian
open _root_.CochainComplex.HomComplex DerivedCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w w'
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  [HasDerivedCategory.{w'} C] {S : ShortComplex C} (hS : S.ShortExact)
  (R : InjectiveResolution S.X₁)

theorem connectingResolution_extMk_hom :
    (R.extMk (ConnectingResolutionCocycle.connectingResolutionQuotient hS R) 2 rfl
      (ConnectingResolutionCocycle.connectingResolutionQuotient_closed hS R)).hom =
        ShiftedHom.map (Cocycle.equivHomShift.symm (ConnectingResolutionCocycle.connectingResolutionCocycle hS R)) Q ≫
          (inv (Q.map R.ι'))⟦(1 : ℤ)⟧' := by
  rw [R.extMk_hom]
  simp only [singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    ShiftedHom.comp_mk₀]
  erw [ShiftedHom.mk₀_id_comp, Category.comp_id]
  rfl

omit [HasExt.{w} C] in
theorem singleConnecting_eq_triangle :
    hS.singleδ = triangleOfSESδ
      (hS.map_of_exact (HomologicalComplex.single C (.up ℤ) 0)) := by
  dsimp [ShortComplex.ShortExact.singleδ]

theorem connectingExtClass_hom_equation :
    hS.extClass.hom ≫ (Q.map R.ι')⟦(1 : ℤ)⟧' =
      -ShiftedHom.map (Cocycle.equivHomShift.symm (ConnectingResolutionCocycle.connectingResolutionCocycle hS R)) Q := by
  rw [ShortComplex.ShortExact.extClass_hom, singleConnecting_eq_triangle]
  exact ConnectingDerivedCocycle.connectingDerivedCocycle
    (S.map (CochainComplex.singleFunctor C 0))
    (hS.map_of_exact (HomologicalComplex.single C (.up ℤ) 0)) R.ι'
    (ConnectingResolutionCocycle.connectingResolutionCochain hS R) (ConnectingResolutionCocycle.connectingResolutionCocycle hS R)
    (ConnectingResolutionCocycle.connectingResolutionCochain_lift hS R) (ConnectingResolutionCocycle.connectingResolutionCochain_d hS R)

theorem connectingExtClass_eq_neg_resolution :
    hS.extClass = -R.extMk (ConnectingResolutionCocycle.connectingResolutionQuotient hS R) 2 rfl
      (ConnectingResolutionCocycle.connectingResolutionQuotient_closed hS R) := by
  ext
  rw [Ext.neg_hom, connectingResolution_extMk_hom]
  have h := congrArg (fun f => f ≫ (inv (Q.map R.ι'))⟦(1 : ℤ)⟧')
    (connectingExtClass_hom_equation hS R)
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, IsIso.hom_inv_id,
    CategoryTheory.Functor.map_id] at h
  exact ((Category.comp_id hS.extClass.hom).symm.trans h).trans (neg_comp _ _)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ConnectingExt
