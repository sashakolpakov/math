import OAI.AlgebraicGeometry.ComplexMultiplication.OpenSupportedCohomologyNormalization
import OAI.AlgebraicGeometry.ComplexMultiplication.InjectiveSupportSheafNormalization

/-! # Relative Unit Class -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RelativeUnitClass

noncomputable section

/-! # The actual relative unit computes the original supported injective inverse -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory Limits _root_.TopologicalSpace _root_.HomologicalComplex
open _root_.AlgebraicGeometry ComplexPoint OAI.AlgebraicTopology.Singular _root_.TopCat.Sheaf

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (S : Closeds (ComplexPoint.Basic.ComplexSchemePoint X)) (n : ℕ)

local notation "Y" => TopCat.of (OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint X)
local notation "P" => OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openInclusionPair (Y) (Opens.infLELeft ⊤ S.compl)
local notation "F" => forget₂ (ModuleCat ℚ) AddCommGrpCat
local notation "K" => ShortComplex.X₁ (OAI.AlgebraicTopology.Singular.RelativeCochainCone.relativeDualCochainShortComplexInt ℚ (P))

local instance CMOriginalRelativeUnitClass.localInstance1 : ∀ W : Opens (ComplexPoint.Basic.ComplexSchemePoint X), ParacompactSpace W := ComplexPoint.Basic.ComplexSchemePoint.openParacompactSpace X

def originalOpenRelativeClass
    (a : (SupportedOpenUnit.originalOpenRelativeShortComplex (Y) S.compl ⊤).X₁.homology (n : ℤ)) :
    AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair
      (Set.univ : Set (ComplexPoint.Basic.ComplexSchemePoint X)) (S : Set (ComplexPoint.Basic.ComplexSchemePoint X))) n :=
  AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ n (AlgebraicTopology.Support.SingularSectionCohomology.Singular.openIntersectionPairIsoSupportComplement (Y) S S.isClosed ⊤).inv
    (AlgebraicTopology.Singular.RelativeCochainConeNaturality.relativeDualCochainCohomologyEquiv ℚ (P) n
      ((((K).sc (n : ℤ)).mapHomologyIso (F)).hom a))

def originalOpenRelativeClassPreimage
    (a : AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair
      (Set.univ : Set (ComplexPoint.Basic.ComplexSchemePoint X)) (S : Set (ComplexPoint.Basic.ComplexSchemePoint X))) n) :
    (SupportedOpenUnit.originalOpenRelativeShortComplex (Y) S.compl ⊤).X₁.homology (n : ℤ) :=
  (((K).sc (n : ℤ)).mapHomologyIso (F)).inv
    ((AlgebraicTopology.Singular.RelativeCochainConeNaturality.relativeDualCochainCohomologyEquiv ℚ (P) n).symm
      (AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ n
        (AlgebraicTopology.Support.SingularSectionCohomology.Singular.openIntersectionPairIsoSupportComplement (Y) S S.isClosed ⊤).hom a))

omit [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom] in
theorem originalOpenRelativeClass_preimage
    (a : AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair
      (Set.univ : Set (ComplexPoint.Basic.ComplexSchemePoint X)) (S : Set (ComplexPoint.Basic.ComplexSchemePoint X))) n) :
    originalOpenRelativeClass X S n (originalOpenRelativeClassPreimage X S n a) = a := by
  let e := ((K).sc (n : ℤ)).mapHomologyIso (F)
  let b := (AlgebraicTopology.Singular.RelativeCochainConeNaturality.relativeDualCochainCohomologyEquiv ℚ (P) n).symm
    (AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ n
      (AlgebraicTopology.Support.SingularSectionCohomology.Singular.openIntersectionPairIsoSupportComplement (Y) S S.isClosed ⊤).hom a)
  have he : e.hom (e.inv b) = b := ConcreteCategory.congr_hom e.inv_hom_id b
  dsimp only [originalOpenRelativeClass, originalOpenRelativeClassPreimage]
  change AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ n _
    (AlgebraicTopology.Singular.RelativeCochainConeNaturality.relativeDualCochainCohomologyEquiv ℚ (P) n (e.hom (e.inv b))) = a
  rw [he, LinearEquiv.apply_symm_apply]
  have hc := congrArg (fun f => AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ n f a)
    (AlgebraicTopology.Support.SingularSectionCohomology.Singular.openIntersectionPairIsoSupportComplement (Y) S S.isClosed ⊤).inv_hom_id
  simpa only [AlgebraicTopology.Singular.CohomologyTo.relativeCohomologyMap_comp, LinearMap.comp_apply,
    AlgebraicTopology.Singular.CohomologyTo.relativeCohomologyMap_id, LinearMap.id_apply] using! hc

theorem originalSupportedInjectiveUnit_relative
    (a : (SupportedOpenUnit.originalOpenRelativeShortComplex (Y) S.compl ⊤).X₁.homology (n : ℤ)) :
    ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveSectionCohomologyEquiv X S ⊤ n
      ((ComplexPoint.Basic.ComplexSchemePoint.complexSupportedSingularInjectiveHomologyIso X S.compl ⊤ (n : ℤ)).hom
        (homologyMap (SupportedOpenUnit.originalOpenSupportUnit (Y) S.compl ⊤).τ₁ (n : ℤ) a)) =
      originalOpenRelativeClass X S n a := by
  let e := ComplexPoint.Basic.ComplexSchemePoint.complexSupportedSingularInjectiveHomologyIso X S.compl ⊤ (n : ℤ)
  let b := homologyMap (SupportedOpenUnit.originalOpenSupportUnit (Y) S.compl ⊤).τ₁ (n : ℤ) a
  have he : e.inv (e.hom b) = b := ConcreteCategory.congr_hom e.hom_inv_id b
  change AlgebraicTopology.Support.SingularSectionCohomology.Singular.supportedRationalSingularSectionCohomologyEquivSupportComplement (Y) S
    S.isClosed ⊤ n (e.inv (e.hom b)) = _
  rw [he]
  change AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ n _
    (AlgebraicTopology.Support.SingularSectionCohomology.Singular.supportedRationalSingularSectionCohomologyEquivRelative (Y) S.compl ⊤ n b) = _
  rw [OpenSupportedCohomologyNormalization.originalOpenSupportedCohomology_normalization]
  rfl

theorem originalRelativeUnit_injectiveSymm
    (a : AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.neighborhoodSupportComplementPair
      (Set.univ : Set (ComplexPoint.Basic.ComplexSchemePoint X)) (S : Set (ComplexPoint.Basic.ComplexSchemePoint X))) n) :
    (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveSectionCohomologyEquiv X S ⊤ n).symm a =
    (ComplexPoint.Basic.ComplexSchemePoint.complexSupportedSingularInjectiveHomologyIso X S.compl ⊤ (n : ℤ)).hom
      (homologyMap (SupportedOpenUnit.originalOpenSupportUnit (Y) S.compl ⊤).τ₁ (n : ℤ)
        (originalOpenRelativeClassPreimage X S n a)) := by
  apply (ComplexPoint.Basic.ComplexSchemePoint.complexSupportInjectiveSectionCohomologyEquiv X S ⊤ n).injective
  rw [AddEquiv.apply_symm_apply, originalSupportedInjectiveUnit_relative]
  exact (originalOpenRelativeClass_preimage X S n a).symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.RelativeUnitClass
