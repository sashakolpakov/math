import OAI.AlgebraicGeometry.Comparison.Betti.ResolutionFromQuasiIso
import OAI.AlgebraicGeometry.Comparison.Betti.IntegrationSheafMap
import OAI.AlgebraicGeometry.Comparison.Betti.SingularInjective
import OAI.AlgebraicGeometry.Comparison.Betti.ResolutionUniqueness

/-! # Singular Injective -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Smooth.SingularInjective.Integration

noncomputable section

/-! The smooth singular resolution maps to the same injective resolution
as ordinary singular cochains. The maps agree on cohomology by their actual augmentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] AlgebraicTopology.DeRham.Comparison.ManifoldSheafLocalPrimitives.manifoldSheafPreadditive
  AlgebraicTopology.DeRham.Comparison.ManifoldSheafLocalPrimitives.manifoldSheafCategoryWithHomology

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def smoothSingularResolutionData : ResolutionExactImage.Data (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf (TopCat.of M)) := by
  have h := AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.quasiIso_manifoldSmoothSheafResolutionMap E M
  exact @ResolutionFromQuasiIso.ofQuasiIsoAugmentation (TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of M)) _ _ _ _
    (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafResolutionMap E M) h

theorem smoothSingularResolutionData_augmentation :
    ResolutionExactImage.cochainAugmentation (smoothSingularResolutionData E M) = AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafResolutionMap E M := by
  have h := AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.quasiIso_manifoldSmoothSheafResolutionMap E M
  exact @ResolutionFromQuasiIso.ofQuasiIsoAugmentation_cochain (TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of M)) _ _ _ _
    (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafResolutionMap E M) h

def smoothSingularToInjective : AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafComplex E M (ModuleCat.of ℂ ℂ) ⟶
    (injectiveResolution (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf (TopCat.of M))).cocomplex :=
  ResolutionExactImage.toInjective (smoothSingularResolutionData E M) (injectiveResolution (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf (TopCat.of M)))

theorem smoothSingularToInjective_normalization :
    AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafResolutionMap E M ≫ smoothSingularToInjective E M =
      (injectiveResolution (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf (TopCat.of M))).ι := by
  rw [← smoothSingularResolutionData_augmentation]
  exact ResolutionExactImage.toInjective_normalization (smoothSingularResolutionData E M)
    (injectiveResolution (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf (TopCat.of M)))

theorem singularSmoothToInjective_cohomology [StronglyLocallyContractibleSpace M] (n : ℕ) :
    HomologicalComplex.homologyMap
      (((FlasqueBiproduct.sections (⊤ : Opens M)).mapHomologicalComplex (.up ℕ)).map
        (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafRestriction E M (ModuleCat.of ℂ ℂ) ≫ smoothSingularToInjective E M)) n =
      HomologicalComplex.homologyMap
        (((FlasqueBiproduct.sections (⊤ : Opens M)).mapHomologicalComplex (.up ℕ)).map
          (SingularInjective.singularSheafToInjective (TopCat.of M))) n := by
  let R := SingularInjective.singularResolutionData (TopCat.of M)
  let I := injectiveResolution (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf (TopCat.of M))
  have hi (q : ℕ) : Injective (I.cocomplex.X q) := I.injective q
  apply ResolutionUniqueness.comparison_homologyMap_eq R I.cocomplex
    (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafRestriction E M (ModuleCat.of ℂ ℂ) ≫ smoothSingularToInjective E M)
    (SingularInjective.singularSheafToInjective (TopCat.of M)) _ (FlasqueBiproduct.sections ⊤) n
  change AlgebraicTopology.Cohomology.Singular.SheafResolution.singularSheafResolutionMap (TopCat.of M) ≫
      (AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafRestriction E M (ModuleCat.of ℂ ℂ) ≫ smoothSingularToInjective E M) =
    AlgebraicTopology.Cohomology.Singular.SheafResolution.singularSheafResolutionMap (TopCat.of M) ≫ SingularInjective.singularSheafToInjective (TopCat.of M)
  erw [← Category.assoc]
  change AlgebraicTopology.Cohomology.Singular.SmoothSheafResolution.manifoldSmoothSheafResolutionMap E M ≫ smoothSingularToInjective E M = _
  rw [smoothSingularToInjective_normalization, SingularInjective.singularSheafToInjective_normalization]
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Smooth.SingularInjective.Integration
