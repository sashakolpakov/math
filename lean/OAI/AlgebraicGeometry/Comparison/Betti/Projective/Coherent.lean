import OAI.AlgebraicGeometry.Comparison.Betti.Projective.Resolution
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.ModuleGlobal
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexPresentationCokernelIso

/-! # Coherent -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.Coherent.Dolbeault

noncomputable section

/-! The original Čech comparison holds for every coherent module on positive-dimensional projective space. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexPresentationCokernelIso.ComplexResolution

attribute [local instance] SheafCohomology.Projective.ComplexMinimalResolution.ComplexResolution.complexResolutionField MvPolynomial.gradedAlgebra
attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveAnalyticCechAcyclic_coherent (n : ℕ) (M : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] : ModuleCechAcyclicity.Dolbeault.projectiveAnalyticCechAcyclic n M := by
  let j : Fin (n + 1) := 0
  obtain ⟨D⟩ := SheafCohomology.Projective.TwoStagePresentation.MvPolynomial.exists_coordinateNegativeTwistPresentation M j
  exact ModuleCechAcyclicity.Dolbeault.projectiveAnalyticCechAcyclic_of_iso n (SheafCohomology.Projective.ComplexPresentationCokernelIso.ComplexResolution.presentationCokernelIso D)
    (ResolutionAnalyticAcyclicity.Dolbeault.projectiveResolutionCokernel_analyticAcyclic n j D.gradedCokernel D.gradedCokernel_nonnegative)

theorem projectiveModuleComparisonIsomorphism_coherent (n : ℕ) (M : (Foundations.Scheme.ProjectiveSpace.projectiveSpace (n + 1)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] : ModuleClosure.Dolbeault.projectiveModuleComparisonIsomorphism (n + 1) M := by
  let j : Fin (n + 2) := 0
  obtain ⟨D⟩ := SheafCohomology.Projective.TwoStagePresentation.MvPolynomial.exists_coordinateNegativeTwistPresentation M j
  exact ModuleClosure.Dolbeault.projectiveModuleComparisonIsomorphism_of_iso (n + 1) (SheafCohomology.Projective.ComplexPresentationCokernelIso.ComplexResolution.presentationCokernelIso D)
    (Resolution.Dolbeault.projectiveResolutionCokernel_comparison n j D.gradedCokernel D.gradedCokernel_nonnegative)

theorem projectiveCoherentOriginalComparison_isIso (n : ℕ) (M : (Foundations.Scheme.ProjectiveSpace.projectiveSpace (n + 1)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap (ModuleFunctor.Dolbeault.projectiveModuleOriginalCechMap (n + 1) M) q) := by
  let : QuasiIso (ModuleFunctor.Dolbeault.projectiveModuleOriginalCechMap (n + 1) M) :=
    projectiveModuleComparisonIsomorphism_coherent n M
  infer_instance

theorem projectiveCoherentGlobalSectionsMap_isIso (n : ℕ) (M : (Foundations.Scheme.ProjectiveSpace.projectiveSpace (n + 1)).Modules)
    [M.IsQuasicoherent] [M.IsFiniteType] : IsIso (ModuleGlobal.Dolbeault.projectiveModuleGlobalSectionsMap (n + 1) M) :=
  ModuleGlobal.Dolbeault.projectiveModuleGlobalSectionsMap_isIso_of_comparison (n + 1) M
    (projectiveModuleComparisonIsomorphism_coherent n M)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.Coherent.Dolbeault
