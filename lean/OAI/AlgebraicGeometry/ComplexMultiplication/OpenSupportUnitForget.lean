import OAI.AlgebraicGeometry.ComplexMultiplication.OpenSupportedCohomologyNormalization
import OAI.AlgebraicGeometry.ComplexMultiplication.SupportedToGlobalHom

/-! # Open Support Unit Forget -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.OpenSupportUnitForget

noncomputable section

/-! # The relative sheafification unit commutes with forgetting support -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory Limits _root_.TopologicalSpace _root_.HomologicalComplex
open OAI.AlgebraicTopology.Singular _root_.TopCat.Sheaf

variable (Y : TopCat.{0}) [T2Space Y] [∀ W : Opens Y, ParacompactSpace W] (U : Opens Y)

theorem originalOpenSupportUnit_forget :
    (SupportedOpenUnit.originalOpenSupportUnit Y U ⊤).τ₁ ≫
      SupportedToGlobalHom.supportedToGlobalSectionComplex Y U (AlgebraicTopology.Support.SingularFlasqueModel.Singular.rationalSingularCochainComplex Y) =
    (SupportedOpenUnit.originalOpenRelativeShortComplex Y U ⊤).f ≫
      SupportedOpenUnit.originalOpenDualToIntegerSections Y ⊤ := by
  exact (SupportedOpenUnit.originalOpenSupportUnit Y U ⊤).comm₁₂

theorem originalOpenSupportUnit_forget_class (n : ℤ)
    (a : (SupportedOpenUnit.originalOpenRelativeShortComplex Y U ⊤).X₁.homology n) :
    homologyMap (SupportedToGlobalHom.supportedToGlobalSectionComplex Y U (AlgebraicTopology.Support.SingularFlasqueModel.Singular.rationalSingularCochainComplex Y)) n
      (homologyMap (SupportedOpenUnit.originalOpenSupportUnit Y U ⊤).τ₁ n a) =
    homologyMap (SupportedOpenUnit.originalOpenDualToIntegerSections Y ⊤) n
      (homologyMap (SupportedOpenUnit.originalOpenRelativeShortComplex Y U ⊤).f n a) := by
  simpa only [HomologicalComplex.homologyMap_comp, AddCommGrpCat.comp_apply] using!
    ConcreteCategory.congr_hom
      (congrArg (fun f => homologyMap f n) (originalOpenSupportUnit_forget Y U)) a

end

end OAI.AlgebraicGeometry.ComplexMultiplication.OpenSupportUnitForget
