import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.BettiSheafMaps
import OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.CochainForget
import OAI.AlgebraicGeometry.DivisorClass.Chern.GlobalIntegrationSheafification

/-! # Smooth Integration -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.SmoothIntegration

noncomputable section

/-! The original global integration cocycle has exactly the native integrated sheaf class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem manifoldSmoothSheafification_closed (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M) (n + 1)) :
    (CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSectionsComplex (Abelian.ManifoldIntegration.abelianManifoldSmoothComplex E M)).d (n + 1) (n + 2)
      ((SmoothGlobalSheafification.manifoldSmoothToAbelianSections E M).f (n + 1) c.val) = 0 := by
  have hc := (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff _ (n + 1) c.val).mp c.property
  have h := ConcreteCategory.congr_hom (C := AddCommGrpCat.{0})
    ((SmoothGlobalSheafification.manifoldSmoothToAbelianSections E M).comm (n + 1) (n + 2)) c.val
  change (CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSectionsComplex (Abelian.ManifoldIntegration.abelianManifoldSmoothComplex E M)).d (n + 1) (n + 2)
    ((SmoothGlobalSheafification.manifoldSmoothToAbelianSections E M).f (n + 1) c.val) =
      (SmoothGlobalSheafification.manifoldSmoothToAbelianSections E M).f (n + 2)
        ((AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).d (n + 1) (n + 2) c.val) at h
  rw [hc, map_zero] at h
  exact h

theorem nativeSmoothCohomologyToSheaf_class (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M) (n + 1)) :
    BettiSheafMaps.nativeSmoothCohomologyToSheaf E M n (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (n + 1) c) =
      AugmentationNaturality.nativeSectionCohomologyMapOfZero (Abelian.ManifoldIntegration.abelianManifoldSmoothComplex E M)
        (Manifold.SmoothZeroResolution.abelianManifoldSmoothComplex_exact E M) (Manifold.SmoothZeroResolution.abelianManifoldSmoothZeroIso E M) n
        ((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSectionsComplex (Abelian.ManifoldIntegration.abelianManifoldSmoothComplex E M)).homologyπ (n + 1)
          (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.abCyclesMk n _ ((SmoothGlobalSheafification.manifoldSmoothToAbelianSections E M).f (n + 1) c.val)
            (manifoldSmoothSheafification_closed E M n c))) := by
  have hc : (ModuleGlobalSectionsForget.complexForgetHomologyIso (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M) (n + 1)).inv
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (n + 1) c) = Complex.CochainForget.complexForgetCycleClass _ n c := by
    rw [← Complex.CochainForget.complexForgetCycleClass_map]
    exact Iso.hom_inv_id_apply _ _
  change AugmentationNaturality.nativeSectionCohomologyMapOfZero _ _ _ n
    (HomologicalComplex.homologyMap (SmoothGlobalSheafification.manifoldSmoothToAbelianSections E M) (n + 1)
      ((ModuleGlobalSectionsForget.complexForgetHomologyIso (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M) (n + 1)).inv
        (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass _ (n + 1) c))) = _
  rw [hc]
  exact congrArg (fun x => AugmentationNaturality.nativeSectionCohomologyMapOfZero (Abelian.ManifoldIntegration.abelianManifoldSmoothComplex E M)
    (Manifold.SmoothZeroResolution.abelianManifoldSmoothComplex_exact E M) (Manifold.SmoothZeroResolution.abelianManifoldSmoothZeroIso E M) n x)
      (SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.homologyMap_abCyclesMk n (SmoothGlobalSheafification.manifoldSmoothToAbelianSections E M) c.val
        ((AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff _ (n + 1) c.val).mp c.property) (manifoldSmoothSheafification_closed E M n c))

theorem nativeSmoothCohomologyToSheaf_integration (form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms E M 2) :
    BettiSheafMaps.nativeSmoothCohomologyToSheaf E M 1
      (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M) 2
        (AlgebraicTopology.DeRham.Comparison.SmoothSimplexClass.smoothSimplexIntegrationCocycle E M 2 form)) =
      IntegratedHodgeSheaf.manifoldIntegratedSheafClass E M (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ form.val)
        (by rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen_d, form.property, map_zero]) := by
  rw [nativeSmoothCohomologyToSheaf_class]
  change CategoryTheory.Sheaf.H.map (Manifold.SmoothZeroResolution.abelianManifoldSmoothZeroIso E M).inv 2
    (SectionCohomologyMap.nativeSectionCohomologyMap _ _ 1 _) = CategoryTheory.Sheaf.H.map (Manifold.SmoothZeroResolution.abelianManifoldSmoothZeroIso E M).inv 2
      (SectionCohomologyMap.nativeSectionCohomologyMap _ _ 1 _)
  apply congrArg (CategoryTheory.Sheaf.H.map (Manifold.SmoothZeroResolution.abelianManifoldSmoothZeroIso E M).inv 2)
  apply congrArg (fun x => SectionCohomologyMap.nativeSectionCohomologyMap (Abelian.ManifoldIntegration.abelianManifoldSmoothComplex E M)
    (Manifold.SmoothZeroResolution.abelianManifoldSmoothComplex_exact E M) 1 x)
  apply congrArg ((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSectionsComplex (Abelian.ManifoldIntegration.abelianManifoldSmoothComplex E M)).homologyπ 2)
  apply (AddCommGrpCat.mono_iff_injective ((CycleClass.Geometric.FlasqueLowDegree.Cycles.sheafGlobalSectionsComplex (Abelian.ManifoldIntegration.abelianManifoldSmoothComplex E M)).iCycles 2)).mp inferInstance
  rw [SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk, SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology.i_abCyclesMk]
  exact (GlobalIntegrationSheafification.manifoldIntegratedSection_global E M form.val).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.SmoothIntegration
