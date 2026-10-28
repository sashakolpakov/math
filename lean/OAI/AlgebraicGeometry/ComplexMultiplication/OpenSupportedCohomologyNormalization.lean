import OAI.AlgebraicGeometry.ComplexMultiplication.OpenSupportConeComparison
import OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalRelativeConeCoefficients

/-! # Open Supported Cohomology Normalization -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.OpenSupportedCohomologyNormalization

noncomputable section

/-! # The literal original supported-cohomology comparison recovers actual relative classes -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Singular _root_.TopCat.Sheaf

variable (Y : TopCat.{0}) [T2Space Y] [∀ W : Opens Y, ParacompactSpace W]
  (U V : Opens Y)

local notation "F" => forget₂ (ModuleCat ℚ) AddCommGrpCat
local notation "P" => OAI.AlgebraicTopology.Singular.SheafCochainOpenCone.openInclusionPair Y (Opens.infLELeft V U)
local notation "S" => OAI.AlgebraicGeometry.ComplexMultiplication.SupportedOpenUnit.originalOpenRelativeShortComplex Y U V

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original local supported equivalence sends the actual kernel unit to its relative class. -/
theorem originalOpenSupportedCohomology_normalization (n : ℕ)
    (a : (S).X₁.homology (n : ℤ)) :
    AlgebraicTopology.Support.SingularSectionCohomology.Singular.supportedRationalSingularSectionCohomologyEquivRelative Y U V n
      (HomologicalComplex.homologyMap (SupportedOpenUnit.originalOpenSupportUnit Y U V).τ₁ (n : ℤ) a) =
    AlgebraicTopology.Singular.RelativeCochainConeNaturality.relativeDualCochainCohomologyEquiv ℚ (P) n
      ((((AlgebraicTopology.Singular.RelativeCochainCone.relativeDualCochainShortComplexInt ℚ (P)).X₁.sc (n : ℤ)).mapHomologyIso (F)).hom a) := by
  let er := HomologicalComplex.homologyMapIso
    (AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionConeIsoRelative ℚ Y (Opens.infLELeft V U)) ((n : ℤ) - 1)
  let ee := HomologicalComplex.homologyMapIso
    (AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestrictionExtendConeIso Y (AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex ℚ Y)
      (Opens.infLELeft V U)) ((n : ℤ) - 1)
  let ec := AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.supportedSectionHomologyIsoRestrictionCone Y U V
    (AlgebraicTopology.Support.SingularFlasqueModel.Singular.rationalSingularCochainComplex Y) (fun _ => inferInstance) (n : ℤ)
  let em := Algebra.Homology.CoconeShortExactNaturality.CochainComplex.mappingCocone.shortExactHomologyIsoCone (S)
    (OpenSupportUnitCone.originalOpenRelativeShortComplex_shortExact Y U V) ((n : ℤ) - 1) n (by omega)
  let := AlgebraicTopology.Singular.SheafCochainOpenCone.openRawToSingularSheafRestrictionCone_quasiIso Y (Opens.infLELeft V U)
  let eu := asIso (HomologicalComplex.homologyMap
    (AlgebraicTopology.Singular.SheafCochainOpenCone.openRawToSingularSheafRestrictionCone ℚ Y (Opens.infLELeft V U)) ((n : ℤ) - 1))
  have hk : ec.hom
      (HomologicalComplex.homologyMap (SupportedOpenUnit.originalOpenSupportUnit Y U V).τ₁ (n : ℤ) a) =
    HomologicalComplex.homologyMap (OpenSupportUnitCone.originalOpenSupportUnitCone Y U V) ((n : ℤ) - 1)
      (em.hom a) := by
    simpa only [ec, em, CategoryTheory.comp_apply] using!
      congrArg (fun f => f a) (OpenSupportUnitCone.originalOpenSupportUnitCone_homology Y U V n)
  have hcone (b : (CochainComplex.mappingCone (S).g).homology ((n : ℤ) - 1)) :
      ee.hom (HomologicalComplex.homologyMap (OpenSupportUnitCone.originalOpenSupportUnitCone Y U V)
        ((n : ℤ) - 1) b) = eu.hom (er.inv b) := by
    have hc := congrArg (fun f : AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionCone ℚ Y (Opens.infLELeft V U) ⟶
        AlgebraicTopology.Singular.SheafCochainOpenCone.openSingularSheafRestrictionCone ℚ Y (Opens.infLELeft V U) => HomologicalComplex.homologyMap f
      ((n : ℤ) - 1) (er.inv b)) (OpenSupportConeComparison.originalOpenSupportUnitCone_raw Y U V)
    simp only [HomologicalComplex.homologyMap_comp, CategoryTheory.comp_apply] at hc
    change ee.hom (HomologicalComplex.homologyMap (OpenSupportUnitCone.originalOpenSupportUnitCone Y U V)
      ((n : ℤ) - 1) (er.hom (er.inv b))) = eu.hom (er.inv b) at hc
    rw [Iso.inv_hom_id_apply] at hc
    exact hc
  change AlgebraicTopology.Singular.SheafCochainOpenCone.openRawSingularRestrictionConeCohomologyEquivRelative ℚ Y (Opens.infLELeft V U) n
    (eu.inv (ee.hom (ec.hom
      (HomologicalComplex.homologyMap (SupportedOpenUnit.originalOpenSupportUnit Y U V).τ₁ (n : ℤ) a)))) = _
  rw [hk, hcone, Iso.hom_inv_id_apply]
  exact CanonicalRelativeConeCoefficients.originalOpenRelativeCone_normalization Y U V n a

end

end OAI.AlgebraicGeometry.ComplexMultiplication.OpenSupportedCohomologyNormalization
