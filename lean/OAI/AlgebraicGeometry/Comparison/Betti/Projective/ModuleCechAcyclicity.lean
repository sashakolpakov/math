import OAI.AlgebraicGeometry.Comparison.Betti.Module.SheafForgetAdditive
import OAI.AlgebraicGeometry.Comparison.Betti.Analytification.ModuleExact
import OAI.AlgebraicGeometry.Comparison.Betti.Cech.AcyclicFiniteSums
import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.AcyclicCover

/-! # Module Cech Acyclicity -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.ModuleCechAcyclicity.Dolbeault

noncomputable section

/-! Acyclicity of actual analytified projective modules is preserved by finite sums and exact cokernels. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Comparison.Betti.Analytification.ModuleExact OAI.AlgebraicGeometry.Comparison.Betti.Cech.AcyclicFiniteSums

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

def projectiveAnalytifiedAdditiveFunctor (n : ℕ) :
    (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)).left.Modules ⥤
      TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n)) :=
  Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) ⋙
    SheafOfModules.toSheaf.{0} (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)))

instance projectiveAnalytifiedAdditiveFunctor_preservesFiniteLimits (n : ℕ) :
    PreservesFiniteLimits (projectiveAnalytifiedAdditiveFunctor n) := by
  let X := Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
  have h₁ : PreservesFiniteLimits (Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X) :=
    Analytification.ModuleExact.holomorphicModuleAnalytification_preservesFiniteLimits X
  have h₂ : PreservesFiniteLimits (SheafOfModules.toSheaf.{0} (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X)) := inferInstance
  exact @comp_preservesFiniteLimits _ _ _ _ _ _ (Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X)
    (SheafOfModules.toSheaf.{0} (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X)) h₁ h₂

instance projectiveAnalytifiedAdditiveFunctor_preservesFiniteColimits (n : ℕ) :
    PreservesFiniteColimits (projectiveAnalytifiedAdditiveFunctor n) := by
  let X := Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
  have h₁ : PreservesFiniteColimits (Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X) := inferInstance
  have h₂ : PreservesFiniteColimits (SheafOfModules.toSheaf.{0} (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X)) :=
    Module.SheafForgetAdditive.Local.moduleSheafForget_preservesFiniteColimits (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X)
  exact @comp_preservesFiniteColimits _ _ _ _ _ _ (Holomorphic.StructureMorphism.algebraicModuleHolomorphicAnalytification X)
    (SheafOfModules.toSheaf.{0} (Holomorphic.StructureMorphism.analyticHolomorphicStructureSheaf X)) h₁ h₂

def projectiveAnalyticCechAcyclic (n : ℕ) (M : (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)).left.Modules) : Prop :=
  SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (Intersections.Dolbeault.projectiveStandardCover n) ((projectiveAnalytifiedAdditiveFunctor n).obj M)

theorem projectiveAnalyticCechAcyclic_twist (n : ℕ) (j : Fin (n + 1)) (d : ℤ) :
    projectiveAnalyticCechAcyclic n (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d) :=
  ProjectiveTwist.AcyclicCover.Dolbeault.projectiveTwistCechIntersectionsAcyclic n j d

theorem projectiveAnalyticCechAcyclic_of_iso (n : ℕ)
    {M N : (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)).left.Modules} (e : M ≅ N)
    (hM : projectiveAnalyticCechAcyclic n M) : projectiveAnalyticCechAcyclic n N :=
  Cech.AcyclicShortExact.cechIntersectionsAcyclic_of_iso (X := TopCat.of (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n)) (Intersections.Dolbeault.projectiveStandardCover n)
    (F := (projectiveAnalytifiedAdditiveFunctor n).obj M) (G := (projectiveAnalytifiedAdditiveFunctor n).obj N)
    ((projectiveAnalytifiedAdditiveFunctor n).mapIso e) hM

theorem projectiveAnalyticCechAcyclic_cokernel (n : ℕ)
    (S : ShortComplex (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)).left.Modules) (hS : S.ShortExact)
    (h₁ : projectiveAnalyticCechAcyclic n S.X₁) (h₂ : projectiveAnalyticCechAcyclic n S.X₂) :
    projectiveAnalyticCechAcyclic n S.X₃ := by
  let : Mono S.f := hS.mono_f
  let : Epi S.g := hS.epi_g
  exact Cech.AcyclicShortExact.cechIntersectionsAcyclic_cokernel (X := TopCat.of (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n)) (Intersections.Dolbeault.projectiveStandardCover n)
    (S.map (projectiveAnalytifiedAdditiveFunctor n)) (hS.map _) h₁ h₂

theorem projectiveAnalyticCechAcyclic_finiteCoproduct (n : ℕ) {ι : Type} [Fintype ι]
    (M : ι → (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)).left.Modules)
    (hM : ∀ i, projectiveAnalyticCechAcyclic n (M i)) :
    projectiveAnalyticCechAcyclic n (∐ M) :=
  Cech.AcyclicShortExact.cechIntersectionsAcyclic_of_iso (X := TopCat.of (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n)) (Intersections.Dolbeault.projectiveStandardCover n)
    (PreservesCoproduct.iso (projectiveAnalytifiedAdditiveFunctor n) M).symm
      (Cech.AcyclicFiniteSums.cechIntersectionsAcyclic_finiteCoproduct (X := TopCat.of (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n)) (Intersections.Dolbeault.projectiveStandardCover n)
        (fun i => (projectiveAnalytifiedAdditiveFunctor n).obj (M i)) hM)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.ModuleCechAcyclicity.Dolbeault
