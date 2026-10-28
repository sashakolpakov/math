import OAI.AlgebraicGeometry.FormalGeometry.Completion.FiniteTorsor.FiberPullback
import OAI.AlgebraicGeometry.FormalGeometry.Completion.ConstantCoherence

/-! # Integer Generator Pullback -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegerGeneratorPullback.Construction

noncomputable section

/-! # Completion: the actual integer generator under inverse image -/

open _root_.CategoryTheory _root_.CategoryTheory.Functor Limits _root_.AlgebraicGeometry Opposite Abelian

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- The cohomological generator is the sheafification of the integer one. -/
theorem proEtIntegerGenerator_eq_unit (X : Scheme.{u}) :
    FiniteTorsor.App.Construction.proEtIntegerGenerator X =
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
          (op (⊤_ X.ProEt)) ⟨1⟩ := by
  change (AddCommGrpCat.uliftZMultiplesAddEquiv _)
    (((constantSheafAdj (Scheme.ProEt.topology X) Ab.{u + 1} terminalIsTerminal).homEquiv _ _)
      (Ext.addEquiv₀ (Ext.mk₀ (𝟙 (ProetalePullback.Construction.proEtIntegerConstant X))))) = _
  rw [show Ext.addEquiv₀ (Ext.mk₀ (𝟙 (ProetalePullback.Construction.proEtIntegerConstant X))) = 𝟙 _ from
    Ext.addEquiv₀.apply_symm_apply _]
  rw [Adjunction.homEquiv_unit, ConstantCoherence.Construction.constantSheafAdj_unit_at]
  rfl

/-- The local generator is the same integer unit at every object. -/
theorem proEtIntegerLocalGenerator_eq_unit (X : Scheme.{u}) (U : X.ProEt) :
    FiniteTorsor.App.Construction.proEtIntegerLocalGenerator X U =
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app (op U) ⟨1⟩ := by
  rw [FiniteTorsor.App.Construction.proEtIntegerLocalGenerator, proEtIntegerGenerator_eq_unit]
  exact (NatTrans.naturality_apply
    (toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))))
    (terminal.from U).op ⟨1⟩).symm

/-- The canonical constant-sheaf map preserves the chosen generator. -/
theorem proEtConstantToPushforward_integerGenerator {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.ProEt) :
    (ConstantCoherence.Construction.proEtConstantToPushforward f (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom.app (op U)
      (FiniteTorsor.App.Construction.proEtIntegerLocalGenerator Y U) =
        FiniteTorsor.App.Construction.proEtIntegerLocalGenerator X ((ProetalePullback.Construction.proEtBaseChange f).obj U) := by
  rw [proEtIntegerLocalGenerator_eq_unit, proEtIntegerLocalGenerator_eq_unit]
  exact ConcreteCategory.congr_hom
    (ConstantCoherence.Construction.proEtConstantToPushforward_unit_app f (AddCommGrpCat.of (ULift.{u + 1} ℤ)) (op U)) ⟨1⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegerGeneratorPullback.Construction
