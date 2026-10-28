import OAI.AlgebraicGeometry.Comparison.Betti.ResolutionExactImage
import OAI.AlgebraicGeometry.Comparison.Betti.InjectiveFlasque
import OAI.AlgebraicGeometry.Comparison.Betti.FlasqueNatQuasiIso
import OAI.AlgebraicTopology.Cohomology.Singular.SheafFlasque

/-! # Singular Injective -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SingularInjective

noncomputable section

/-!
# Actual singular cochains compute an injective sheaf resolution

The singular sheaf resolution is compared with an injective resolution by
the constructed augmentation-preserving chain map. Both complexes are
degreewise flasque, so the proved open-section theorem makes this a
quasi-isomorphism on global sections. The singular sheafification map is
the original map on singular cochains.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.SheafFlasque

attribute [local instance] AlgebraicTopology.Cohomology.Singular.StalkExactnessAt.stalkModulesForget₂PreservesFilteredColimits
  AlgebraicTopology.Cohomology.Singular.StalkExactnessAt.stalkModulesForgetPreservesFilteredColimits InjectiveFlasque.complexModuleLimits

variable (M : TopCat.{0}) [StronglyLocallyContractibleSpace M]

/-- All fields are the already proved properties of the genuine singular sheaf complex. -/
def singularResolutionData : ResolutionExactImage.Data (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf M) where
  complex := AlgebraicTopology.Cohomology.Singular.SheafResolution.singularSheafComplex M
  augmentation := AlgebraicTopology.Cohomology.Singular.SheafResolution.locallyConstantSingularSheafAugmentation M
  augmentation_d := AlgebraicTopology.Cohomology.Singular.SheafResolution.locallyConstantSingularSheafAugmentation_d M
  isKernel := AlgebraicTopology.Cohomology.Singular.SheafResolution.locallyConstantSingularSheafAugmentation_isKernel M
  exact_succ := AlgebraicTopology.Cohomology.Singular.SheafResolution.singularSheafComplex_exactAt_succ M

def singularInjectiveResolution : InjectiveResolution (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf M) :=
  injectiveResolution (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf M)

/-- The constructed cochain comparison extends the actual locally constant augmentation. -/
def singularSheafToInjective : AlgebraicTopology.Cohomology.Singular.SheafResolution.singularSheafComplex M ⟶ (singularInjectiveResolution M).cocomplex :=
  ResolutionExactImage.toInjective (singularResolutionData M) (singularInjectiveResolution M)

theorem singularSheafToInjective_normalization :
    AlgebraicTopology.Cohomology.Singular.SheafResolution.singularSheafResolutionMap M ≫ singularSheafToInjective M = (singularInjectiveResolution M).ι :=
  ResolutionExactImage.toInjective_normalization (singularResolutionData M) (singularInjectiveResolution M)

theorem singularSheafToInjective_quasiIso : QuasiIso (singularSheafToInjective M) :=
  ResolutionExactImage.toInjective_quasiIso (singularResolutionData M) (singularInjectiveResolution M)

variable [MetrizableSpace M]

/-- The actual comparison remains a quasi-isomorphism after taking global sections. -/
theorem singularSheafToInjective_sections_quasiIso :
    QuasiIso (((FlasqueBiproduct.sections (⊤ : Opens M)).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (singularSheafToInjective M)) :=
  FlasqueNatQuasiIso.nat_sections_quasiIso (singularSheafToInjective M)
    (AlgebraicTopology.Cohomology.Singular.SheafFlasque.sheafifiedSingularCochains_isFlasque_of_metrizable (ModuleCat.of ℂ ℂ) M)
    (fun n => InjectiveFlasque.injective_flasque ((singularInjectiveResolution M).cocomplex.X n))
    (singularSheafToInjective_quasiIso M) ⊤

/-- Genuine ordinary singular cochains map to global sections of the injective resolution. -/
def singularToInjectiveSections : AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) M ⟶
    (((FlasqueBiproduct.sections (⊤ : Opens M)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (singularInjectiveResolution M).cocomplex) :=
  AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℂ ℂ) M ≫
    ((FlasqueBiproduct.sections (⊤ : Opens M)).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (singularSheafToInjective M)

theorem singularToInjectiveSections_quasiIso : QuasiIso (singularToInjectiveSections M) := by
  let : MetricSpace M := metrizableSpaceMetric M
  have h₁ : QuasiIso (AlgebraicTopology.Cohomology.Singular.LocallyZeroCochains.singularCochainsToSheafSections (ModuleCat.of ℂ ℂ) M) :=
    AlgebraicTopology.Cohomology.Singular.ParacompactComparison.quasiIso_singularCochainsToSheafSections_of_paracompact ℂ M
  have h₂ : QuasiIso (((FlasqueBiproduct.sections (⊤ : Opens M)).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (singularSheafToInjective M)) :=
    singularSheafToInjective_sections_quasiIso M
  unfold singularToInjectiveSections
  exact quasiIso_comp _ _ (hφ := h₁) (hφ' := h₂)

/-- This cohomology isomorphism is induced by the original singular cochains and the normalized comparison. -/
def singularInjectiveSectionsCohomologyIso (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) M n ≅
      ((((FlasqueBiproduct.sections (⊤ : Opens M)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (singularInjectiveResolution M).cocomplex).homology n) := by
  have := singularToInjectiveSections_quasiIso M
  exact isoOfQuasiIsoAt (singularToInjectiveSections M) n

end

end OAI.AlgebraicGeometry.Comparison.Betti.SingularInjective
