import OAI.AlgebraicGeometry.ComplexMultiplication.ForgetSupportHypercohomology
import OAI.AlgebraicGeometry.ComplexMultiplication.OrdinarySingularInjectiveComparison
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RelativeAbsoluteClass

/-! # Relative Forget Class -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RelativeForgetClass

noncomputable section

section

/-! # Forgetting the actual relative unit gives the canonical ordinary class -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory Limits _root_.TopologicalSpace _root_.HomologicalComplex
open _root_.AlgebraicGeometry ComplexPoint OAI.AlgebraicTopology.Singular _root_.TopCat.Sheaf

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (S : Closeds (ComplexPoint.Basic.ComplexSchemePoint X)) (n : ℕ)
local notation "Y" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
local instance CMOriginalRelativeForgetNormalization.localInstance1 : ∀ W : Opens (ComplexPoint.Basic.ComplexSchemePoint X), ParacompactSpace W := ComplexPoint.Basic.ComplexSchemePoint.openParacompactSpace X

theorem originalRelativeUnit_forgetSupport
    (a : (SupportedOpenUnit.originalOpenRelativeShortComplex (Y) S.compl ⊤).X₁.homology (n : ℤ)) :
    ComplexPoint.Basic.ComplexSchemePoint.forgetSupport ℚ X S n
      ((ComplexPoint.Basic.ComplexSchemePoint.rationalSupportAddEquivSupportedInjectiveHomology X S n).symm
        ((ComplexPoint.Basic.ComplexSchemePoint.complexSupportedSingularInjectiveHomologyIso X S.compl ⊤ (n : ℤ)).hom
          (homologyMap (SupportedOpenUnit.originalOpenSupportUnit (Y) S.compl ⊤).τ₁ (n : ℤ) a))) =
    CanonicalSheafComparison.canonicalSingularToConstantSheafAddEquiv ℚ X n
      ((Coefficient.SheafComparison.rawSingularHomologyIso ℚ (Y) n).hom (RelativeAbsoluteClass.originalRelativeRawAbsoluteClass X S n a)) := by
  apply (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℚ X n).symm.injective
  let f := ComplexPoint.Basic.ComplexSchemePoint.ambientRationalInjectiveAugmentation X
  apply (Localization.SmallShiftedHom.postcompEquiv f
    (show QuasiIso f from inferInstance)).injective
  change ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X f (n : ℤ) _ = ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X f (n : ℤ) _
  rw [ForgetSupportHypercohomology.forgetSupport_hypercohomology, AddEquiv.apply_symm_apply,
    SupportedInjectiveGlobalSquare.supportedInjectiveGlobal_class, OpenSupportUnitForget.originalOpenSupportUnit_forget_class,
    OrdinarySingularInjectiveComparison.ordinarySingularInjective_comparison]
  congr 2
  let b := homologyMap (AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularCochainComplexIntIsoDual ℚ (Y) ⊤).inv (n : ℤ)
    (homologyMap (SupportedOpenUnit.originalOpenRelativeShortComplex (Y) S.compl ⊤).f (n : ℤ) a)
  have h := OpenGlobalSingularNormalization.originalOpenRawGlobalInteger_normalization X n b
  have hi : (Coefficient.SheafComparison.singularGlobalIntegerHomologyIso ℚ X n).inv
      ((Coefficient.SheafComparison.singularGlobalIntegerHomologyIso ℚ X n).hom
        (homologyMap (SupportedOpenUnit.originalOpenRawToIntegerSections (Y) ⊤) (n : ℤ) b)) =
      homologyMap (SupportedOpenUnit.originalOpenRawToIntegerSections (Y) ⊤) (n : ℤ) b :=
    ConcreteCategory.congr_hom (Coefficient.SheafComparison.singularGlobalIntegerHomologyIso ℚ X n).hom_inv_id _
  have hl : homologyMap (SupportedOpenUnit.originalOpenDualToIntegerSections (Y) ⊤) (n : ℤ)
      (homologyMap (SupportedOpenUnit.originalOpenRelativeShortComplex (Y) S.compl ⊤).f (n : ℤ) a) =
      homologyMap (SupportedOpenUnit.originalOpenRawToIntegerSections (Y) ⊤) (n : ℤ) b := by
    simp only [SupportedOpenUnit.originalOpenDualToIntegerSections,
      HomologicalComplex.homologyMap_comp, AddCommGrpCat.comp_apply]
    rfl
  have ht := congrArg (fun z => (Coefficient.SheafComparison.singularGlobalIntegerHomologyIso ℚ X n).inv z) h
  simpa only using! hl.trans (hi.symm.trans ht)

end

/-! # The original forget-support map is the canonical absolute image of every relative class -/
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory Limits _root_.TopologicalSpace _root_.HomologicalComplex
open _root_.AlgebraicGeometry ComplexPoint OAI.AlgebraicTopology.Singular _root_.TopCat.Sheaf
variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (S : Closeds (ComplexPoint.Basic.ComplexSchemePoint X)) (n : ℕ)
local notation "Y" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
local instance CMOriginalRelativeForgetClass.localInstance1 : ∀ W : Opens (ComplexPoint.Basic.ComplexSchemePoint X), ParacompactSpace W := ComplexPoint.Basic.ComplexSchemePoint.openParacompactSpace X

theorem originalRelativeClass_forgetSupport
    (a : AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ
      (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (Set.univ : Set (ComplexPoint.Basic.ComplexSchemePoint X)) S) n) :
    ComplexPoint.Basic.ComplexSchemePoint.forgetSupport ℚ X S n
      ((ComplexPoint.Basic.ComplexSchemePoint.rationalSupportAddEquivSupportedInjectiveHomology X S n).symm
        ((ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveSectionCohomologyEquiv X S ⊤ n).symm a)) =
    CanonicalSheafComparison.canonicalSingularToConstantSheafAddEquiv ℚ X n
      (AlgebraicTopology.Singular.CohomologyTo.cohomologyMap ℚ n (Opens.inclusionTopIso (Y)).inv
        (AlgebraicTopology.Singular.CohomologyTo.relativeCohomologyToAbsolute ℚ
          (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (Set.univ : Set (ComplexPoint.Basic.ComplexSchemePoint X)) S) n a)) := by
  let b := RelativeUnitClass.originalOpenRelativeClassPreimage X S n a
  have hi := RelativeUnitClass.originalRelativeUnit_injectiveSymm X S n a
  have hd := congrArg (fun z => ComplexPoint.Basic.ComplexSchemePoint.forgetSupport ℚ X S n
    ((ComplexPoint.Basic.ComplexSchemePoint.rationalSupportAddEquivSupportedInjectiveHomology X S n).symm z)) hi
  have hu := originalRelativeUnit_forgetSupport X S n b
  have hr := RelativeAbsoluteClass.originalRelativeRawAbsoluteClass_normalization X S n b
  have hc := RelativeUnitClass.originalOpenRelativeClass_preimage X S n a
  have ht := congrArg (fun z => AlgebraicTopology.Singular.CohomologyTo.cohomologyMap ℚ n (Opens.inclusionTopIso (Y)).inv
    (AlgebraicTopology.Singular.CohomologyTo.relativeCohomologyToAbsolute ℚ
      (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair (Set.univ : Set (ComplexPoint.Basic.ComplexSchemePoint X)) S) n z)) hc
  simpa only using! hd.trans (hu.trans
    (congrArg (CanonicalSheafComparison.canonicalSingularToConstantSheafAddEquiv ℚ X n) (hr.trans ht)))

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RelativeForgetClass
