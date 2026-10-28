import OAI.AlgebraicGeometry.ComplexMultiplication.SupportedOpenUnit
import OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalKernelConeFunctor

/-! # Open Support Unit Cone -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.OpenSupportUnitCone

noncomputable section

/-! # The actual supported unit has the original positive restriction-cone normalization -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Singular _root_.TopCat.Sheaf

variable (Y : TopCat.{0}) [T2Space Y] [∀ W : Opens Y, ParacompactSpace W]
  (U V : Opens Y)

local notation "FI" => Functor.mapHomologicalComplex
  (forget₂ (ModuleCat ℚ) AddCommGrpCat) (ComplexShape.up ℤ)
local notation "K" => OAI.AlgebraicTopology.Support.SingularFlasqueModel.Singular.rationalSingularCochainComplex Y
local notation "S" => OAI.AlgebraicGeometry.ComplexMultiplication.SupportedOpenUnit.originalOpenRelativeShortComplex Y U V
local notation "T" => OAI.AlgebraicGeometry.ComplexMultiplication.SupportedOpenUnit.originalOpenSupportShortComplex Y U V

omit [T2Space Y] [∀ W : Opens Y, ParacompactSpace W] in
set_option backward.isDefEq.respectTransparency false in
/-- The actual chain-dual relative sequence remains short exact after forgetting scalars. -/
theorem originalOpenRelativeShortComplex_shortExact : (S).ShortExact :=
  (AlgebraicTopology.Singular.RelativeCochainG.relativeDualCochainShortComplexInt_shortExact ℚ
    (AlgebraicTopology.Singular.SheafCochainOpenCone.openInclusionPair Y (Opens.infLELeft V U))).map_of_exact (FI)

/-- The actual supported-section sequence is short exact by flasqueness. -/
theorem originalOpenSupportShortComplex_shortExact : (T).ShortExact :=
  AlgebraicTopology.Support.FlasqueComparison.TopCat.Sheaf.supportRestrictionSectionsComplexShortComplex_shortExact_of_flasque Y U V (K)
    (fun _ => inferInstance)

/-- The actual map of restriction cones, including the literal intersection identification. -/
def originalOpenSupportUnitCone :
    CochainComplex.mappingCone (S).g ⟶
      CochainComplex.mappingCone
        (AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.sectionComplexRestriction Y (.up ℤ) (K) (Opens.infLELeft V U)) :=
  CochainComplex.mappingCone.map (S).g (T).g
    (SupportedOpenUnit.originalOpenSupportUnit Y U V).τ₂ (SupportedOpenUnit.originalOpenSupportUnit Y U V).τ₃
    (SupportedOpenUnit.originalOpenSupportUnit Y U V).comm₂₃.symm ≫
      (AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.supportRestrictionSectionsConeIso Y U V (K)).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Taking cohomology of the unit gives precisely the positive short-exact cone comparison. -/
theorem originalOpenSupportUnitCone_homology (n : ℕ) :
    HomologicalComplex.homologyMap (SupportedOpenUnit.originalOpenSupportUnit Y U V).τ₁ (n : ℤ) ≫
      (AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.supportedSectionHomologyIsoRestrictionCone Y U V (K) (fun _ => inferInstance)
        (n : ℤ)).hom =
    (Algebra.Homology.CoconeShortExactNaturality.CochainComplex.mappingCocone.shortExactHomologyIsoCone (S)
      (originalOpenRelativeShortComplex_shortExact Y U V) ((n : ℤ) - 1) n (by omega)).hom ≫
      HomologicalComplex.homologyMap (originalOpenSupportUnitCone Y U V) ((n : ℤ) - 1) := by
  have h := Algebra.Homology.DerivedCategoryConeNaturality.CochainComplex.mappingCocone.shortExactHomologyIsoCone_naturality
    (SupportedOpenUnit.originalOpenSupportUnit Y U V) (originalOpenRelativeShortComplex_shortExact Y U V)
    (originalOpenSupportShortComplex_shortExact Y U V) ((n : ℤ) - 1) n (by omega)
  have h' := congrArg (fun g => g ≫
    HomologicalComplex.homologyMap (AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.supportRestrictionSectionsConeIso Y U V (K)).hom
      ((n : ℤ) - 1)) h
  simpa only [originalOpenSupportUnitCone, HomologicalComplex.homologyMap_comp,
    SupportedOpenUnit.originalOpenSupportShortComplex, AlgebraicTopology.Support.SectionRestrictionCone.TopCat.Sheaf.supportedSectionHomologyIsoRestrictionCone,
    Algebra.Homology.CoconeShortExactNaturality.CochainComplex.mappingCocone.shortExactHomologyIsoCone,
    Iso.trans_hom, Iso.symm_hom, asIso_hom,
    HomologicalComplex.homologyMapIso_hom, Category.assoc] using h'

end

end OAI.AlgebraicGeometry.ComplexMultiplication.OpenSupportUnitCone
