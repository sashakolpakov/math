import OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.SmoothZeroResolution
import OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DeRhamSecondQuotient
import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.AugmentedResolution

/-! # Integration Connecting -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.IntegrationConnecting

noncomputable section

/-! The de Rham connecting class is computed by the original integration map in an actual resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def manifoldSmoothNativeResolution := injectiveResolution ((Abelian.ManifoldIntegration.abelianManifoldSmoothComplex E M).homology 0)

def manifoldSmoothNativeLift : Abelian.ManifoldIntegration.abelianManifoldSmoothComplex E M ⟶ (manifoldSmoothNativeResolution E M).cocomplex :=
  HodgeConjecture.DegreeTwo.ResolutionHomotopy.Constructions.resolutionLift _ (SmoothZeroResolution.abelianManifoldSmoothComplex_exact E M) (manifoldSmoothNativeResolution E M)

def manifoldIntegrationNativeLift : Abelian.ManifoldIntegration.abelianManifoldDeRhamComplex E M ⟶ (manifoldSmoothNativeResolution E M).cocomplex :=
  Abelian.ManifoldIntegration.abelianManifoldIntegration E M ≫ manifoldSmoothNativeLift E M

theorem manifoldIntegrationNativeLift_augmentation :
    Abelian.ManifoldDeRham.abelianManifoldLocallyConstantInclusion E M ≫ (manifoldIntegrationNativeLift E M).f 0 =
      (SmoothZeroResolution.abelianManifoldSmoothZeroIso E M).hom ≫ (manifoldSmoothNativeResolution E M).ι.f 0 := by
  change Abelian.ManifoldDeRham.abelianManifoldLocallyConstantInclusion E M ≫
    ((Abelian.ManifoldIntegration.abelianManifoldIntegration E M).f 0 ≫ (manifoldSmoothNativeLift E M).f 0) = _
  rw [← Category.assoc, Abelian.ManifoldIntegration.abelianManifoldIntegration_augmentation]
  exact AugmentedCochainZeroIso.augmentedCochainZeroIso_resolutionLift _ _ _ _
    (SmoothZeroResolution.abelianManifoldSmoothComplex_exact E M) (manifoldSmoothNativeResolution E M)

theorem manifoldIntegrationNativeLift_section (n : ℕ) (U : Opens M)
    (form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) :
    ((manifoldIntegrationNativeLift E M).f n).hom.app (op U) form =
      ((manifoldSmoothNativeLift E M).f n).hom.app (op U)
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology (TopCat.of M))
          ((AlgebraicTopology.Cohomology.Singular.ManifoldSmoothPresheaf.manifoldSmoothPresheafComplex E M (ModuleCat.of ℂ ℂ)).X n)).app (op U)
            ((AlgebraicTopology.DeRham.Comparison.ManifoldOpenIntegration.manifoldOpenIntegration E U).f n form)) := rfl

theorem manifoldIntegrationNativeLift_closed
    (form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (⊤ : Opens M) 2) (hform : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d form = 0) :
    ((manifoldSmoothNativeResolution E M).cocomplex.d 2 3).hom.app (op (⊤ : Opens M))
      (((manifoldIntegrationNativeLift E M).f 2).hom.app (op (⊤ : Opens M)) form) = 0 := by
  apply Chern.Sheaf.AugmentedResolution.sheafCochainMap_section_closed
  change ((Abelian.ManifoldIntegration.abelianManifoldDeRhamComplex E M).d 2 3).hom.app (op (⊤ : Opens M)) form = 0
  rw [Abelian.ManifoldIntegration.abelianManifoldDeRhamComplex_d]
  exact hform

theorem manifoldDeRhamConnectingClass_integration
    (s : (DeRhamSecondQuotient.manifoldDeRhamSecondQuotient E M).obj.obj (op (⊤ : Opens M)))
    (form : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (⊤ : Opens M) 2) (hform : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d form = 0)
    (hs : (DeRhamSecondQuotient.manifoldDeRhamSecondQuotientInclusion E M).hom.app (op (⊤ : Opens M)) s = form) :
    CategoryTheory.Sheaf.H.map (SmoothZeroResolution.abelianManifoldSmoothZeroIso E M).hom 2
      (DeRhamSecondQuotient.manifoldDeRhamConnectingClass E M s) =
      -Chern.Sheaf.ResolutionClasses.sheafResolutionCycleClass (manifoldSmoothNativeResolution E M) 2
        (((manifoldIntegrationNativeLift E M).f 2).hom.app (op (⊤ : Opens M)) form)
        (manifoldIntegrationNativeLift_closed E M form hform) := by
  have : Mono (Abelian.ManifoldDeRham.abelianManifoldLocallyConstantInclusion E M) := Abelian.ManifoldDeRham.abelianManifoldLocallyConstantInclusion_mono E M
  have hK : (AugmentedResolutionComparison.augmentedZeroSequence (Abelian.ManifoldIntegration.abelianManifoldDeRhamComplex E M)
      (Abelian.ManifoldDeRham.abelianManifoldLocallyConstantInclusion E M) (Abelian.ManifoldIntegration.abelianManifoldDeRhamComplex_augmentation_d E M)).Exact := by
    rw [Abelian.ManifoldIntegration.abelianManifoldDeRhamComplex_zeroSequence]
    exact Abelian.ManifoldDeRham.abelianManifoldDeRhamZeroSequence_exact E M
  exact Chern.Sheaf.AugmentedResolution.sheafTwoStepBoundary_cochain_resolution (Abelian.ManifoldIntegration.abelianManifoldDeRhamComplex E M)
    (Abelian.ManifoldDeRham.abelianManifoldLocallyConstantInclusion E M) (Abelian.ManifoldIntegration.abelianManifoldDeRhamComplex_augmentation_d E M) hK
    (manifoldSmoothNativeResolution E M) (SmoothZeroResolution.abelianManifoldSmoothZeroIso E M).hom
    (manifoldIntegrationNativeLift E M) (manifoldIntegrationNativeLift_augmentation E M)
    s form hform hs

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.IntegrationConnecting
