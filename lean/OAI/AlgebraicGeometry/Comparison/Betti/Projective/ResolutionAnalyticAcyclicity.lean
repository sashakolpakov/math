import OAI.AlgebraicGeometry.Comparison.Betti.Projective.NegativePowerSums
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexResolutionTerminal

/-! # Resolution Analytic Acyclicity -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.ResolutionAnalyticAcyclicity.Dolbeault

noncomputable section

/-! Finite graded resolutions prove analytic intersection acyclicity for their actual cokernel sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.SheafCohomology.Projective.ComplexResolutionTerminal.ComplexResolution

attribute [local instance] SheafCohomology.Projective.ComplexMinimalResolution.ComplexResolution.complexResolutionField MvPolynomial.gradedAlgebra
attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveResolutionFreeSheaf_analyticAcyclic (n : ℕ) (j : Fin (n + 1))
    (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule (Fin (n + 1)) Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤)) :
    ModuleCechAcyclicity.Dolbeault.projectiveAnalyticCechAcyclic n (SheafCohomology.Projective.ComplexMinimalResolution.ComplexResolution.freeSheaf j D) :=
  NegativePowerSums.Dolbeault.projectiveAnalyticCechAcyclic_negativePowerSum n j (SheafCohomology.Projective.GradedMinimalFiniteCover.augmentationFinWeight D)

theorem projectiveResolutionCokernel_analyticAcyclic_of_projective_syzygy
    (n : ℕ) (j : Fin (n + 1)) (q : ℕ)
    (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule (Fin (n + 1)) Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤))
    (hD : SheafCohomology.Projective.GradedNonnegativeSyzygy.HasNonnegativeGrading D)
    (hq : Projective (SheafCohomology.Projective.GradedSyzygyDimension.gradedModuleObject (SheafCohomology.Projective.GradedMinimalSyzygy.iteratedMinimalGradedSyzygy D q))) :
    ModuleCechAcyclicity.Dolbeault.projectiveAnalyticCechAcyclic n (SheafCohomology.Projective.ComplexResolutionCokernel.ComplexResolution.cokernelSheaf j D hD) := by
  induction q generalizing D with
  | zero =>
      let : Projective (SheafCohomology.Projective.GradedSyzygyDimension.gradedModuleObject D) := hq
      exact ModuleCechAcyclicity.Dolbeault.projectiveAnalyticCechAcyclic_of_iso n
        (SheafCohomology.Projective.ComplexResolutionTerminal.ComplexResolution.cokernelSheafIsoFreeOfProjective j D hD).symm
        (projectiveResolutionFreeSheaf_analyticAcyclic n j D)
  | succ q ih =>
      let D' := SheafCohomology.Projective.GradedMinimalSyzygy.minimalGradedSyzygy D
      let hD' := SheafCohomology.Projective.GradedNonnegativeSyzygy.minimalGradedSyzygy_nonnegative D hD
      have h₁ : ModuleCechAcyclicity.Dolbeault.projectiveAnalyticCechAcyclic n (SheafCohomology.Projective.ComplexResolutionCokernel.ComplexResolution.cokernelSheaf j D' hD') :=
        ih D' hD' hq
      exact ModuleCechAcyclicity.Dolbeault.projectiveAnalyticCechAcyclic_cokernel n (SheafCohomology.Projective.ComplexResolutionCokernel.ComplexResolution.syzygyShortComplex j D hD)
        (SheafCohomology.Projective.ComplexResolutionCokernel.ComplexResolution.syzygyShortComplex_shortExact j D hD) h₁
        (projectiveResolutionFreeSheaf_analyticAcyclic n j D)

theorem projectiveResolutionCokernel_analyticAcyclic (n : ℕ) (j : Fin (n + 1))
    (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule (Fin (n + 1)) Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤))
    (hD : SheafCohomology.Projective.GradedNonnegativeSyzygy.HasNonnegativeGrading D) :
    ModuleCechAcyclicity.Dolbeault.projectiveAnalyticCechAcyclic n (SheafCohomology.Projective.ComplexResolutionCokernel.ComplexResolution.cokernelSheaf j D hD) :=
  projectiveResolutionCokernel_analyticAcyclic_of_projective_syzygy n j (n + 1) D hD
    (SheafCohomology.Projective.GradedMinimalSyzygy.iteratedMinimalGradedSyzygy_projective (n + 1) D)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.ResolutionAnalyticAcyclicity.Dolbeault
