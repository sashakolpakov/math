import OAI.AlgebraicGeometry.DivisorClass.Chern.Supported.SectionQuasiIso
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueResolutionComparison

/-! # Flasque Supported Comparison -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.FlasqueSupportedComparison

noncomputable section

/-! Actual quasi-isomorphisms of flasque resolutions compute sections with any prescribed closed support. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.FlasqueResolutionComparison.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{0}} (O : Opens X)

theorem rationalFlasqueSupportedSections_quasiIso
    {K L : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ} (f : K ⟶ L)
    (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
    (hL : ∀ n, TopCat.Sheaf.IsFlasque (L.X n)) [QuasiIso f] (U : Opens X) :
    QuasiIso (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (Supported.SectionQuasiIso.supportedSheafComplexMap O f)) :=
  Supported.SectionQuasiIso.supportedSheafSectionsMap_quasiIso O f hK hL U
    (HodgeConjecture.DegreeTwo.FlasqueResolutionComparison.Constructions.rationalFlasqueSections_quasiIso f hK hL U)
    (HodgeConjecture.DegreeTwo.FlasqueResolutionComparison.Constructions.rationalFlasqueSections_quasiIso f hK hL (U ⊓ O))

variable (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
variable (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n)) (he : ∀ n, K.ExactAt (n+1))
variable (I : InjectiveResolution (K.homology 0))

include hK in
theorem flasqueResolutionLift_supported_quasiIso (U : Opens X) :
    QuasiIso (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (Supported.SectionQuasiIso.supportedSheafComplexMap O (HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.resolutionLift K he I))) := by
  have := HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.resolutionLift_quasiIso K he I
  exact rationalFlasqueSupportedSections_quasiIso O (HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.resolutionLift K he I) hK
    (fun n => HodgeConjecture.DegreeTwo.FlasqueInjectives.Constructions.injectiveModuleSheaf_isFlasque (I.cocomplex.X n)) U

def flasqueSupportedResolutionCohomologyIso (U : Opens X) (n : ℕ) :
    (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex O K)).homology n ≅
      (CycleClass.Geometric.SupportStalkVanishes.Cohomology.moduleSheafSectionsComplex U (CycleClass.Geometric.SupportStalkVanishes.Cohomology.supportedSheafComplex O I.cocomplex)).homology n := by
  have := flasqueResolutionLift_supported_quasiIso O K hK he I U
  exact isoOfQuasiIsoAt
    (((CycleClass.Geometric.SheafClosedSupport.Cohomology.moduleSheafSections (R := ℚ) U).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (Supported.SectionQuasiIso.supportedSheafComplexMap O (HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.resolutionLift K he I))) n

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.FlasqueSupportedComparison
