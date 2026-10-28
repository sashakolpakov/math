import OAI.AlgebraicGeometry.Comparison.Betti.Projective.ResolutionAnalyticAcyclicity
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.ResolutionStep
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.CechExact

/-! # Resolution -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.Resolution.Dolbeault

noncomputable section

/-! The original projective comparison is invertible on cokernels of the finite graded resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

attribute [local instance] SheafCohomology.Projective.ComplexMinimalResolution.ComplexResolution.complexResolutionField MvPolynomial.gradedAlgebra
attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveResolutionFreeSheaf_comparison (n : ℕ) (j : Fin (n + 2))
    (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule (Fin (n + 2)) Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤)) :
    ModuleClosure.Dolbeault.projectiveModuleComparisonIsomorphism (n + 1) (SheafCohomology.Projective.ComplexMinimalResolution.ComplexResolution.freeSheaf j D) :=
  NegativePowerSums.Dolbeault.projectiveModuleComparisonIsomorphism_negativePowerSum n j (SheafCohomology.Projective.GradedMinimalFiniteCover.augmentationFinWeight D)

theorem projectiveResolutionCokernel_comparison_of_projective_syzygy
    (n : ℕ) (j : Fin (n + 2)) (q : ℕ)
    (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule (Fin (n + 2)) Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤))
    (hD : SheafCohomology.Projective.GradedNonnegativeSyzygy.HasNonnegativeGrading D)
    (hq : Projective (SheafCohomology.Projective.GradedSyzygyDimension.gradedModuleObject (SheafCohomology.Projective.GradedMinimalSyzygy.iteratedMinimalGradedSyzygy D q))) :
    ModuleClosure.Dolbeault.projectiveModuleComparisonIsomorphism (n + 1) (SheafCohomology.Projective.ComplexResolutionCokernel.ComplexResolution.cokernelSheaf j D hD) := by
  induction q generalizing D with
  | zero =>
      let : Projective (SheafCohomology.Projective.GradedSyzygyDimension.gradedModuleObject D) := hq
      exact ModuleClosure.Dolbeault.projectiveModuleComparisonIsomorphism_of_iso (n + 1)
        (SheafCohomology.Projective.ComplexResolutionTerminal.ComplexResolution.cokernelSheafIsoFreeOfProjective j D hD).symm
        (projectiveResolutionFreeSheaf_comparison n j D)
  | succ q ih =>
      let D' := SheafCohomology.Projective.GradedMinimalSyzygy.minimalGradedSyzygy D
      let hD' := SheafCohomology.Projective.GradedNonnegativeSyzygy.minimalGradedSyzygy_nonnegative D hD
      let : (SheafCohomology.Projective.ComplexResolutionCokernel.ComplexResolution.cokernelSheaf j D' hD').IsQuasicoherent := SheafCohomology.Projective.ComplexResolutionCokernel.ComplexResolution.cokernelSheaf_quasicoherent j D' hD'
      have h₁ : ModuleClosure.Dolbeault.projectiveModuleComparisonIsomorphism (n + 1) (SheafCohomology.Projective.ComplexResolutionCokernel.ComplexResolution.cokernelSheaf j D' hD') :=
        ih D' hD' hq
      exact ResolutionStep.Dolbeault.projectiveModuleComparisonIsomorphism_resolution_step (n + 1) (SheafCohomology.Projective.ComplexResolutionCokernel.ComplexResolution.syzygyShortComplex j D hD)
        (SheafCohomology.Projective.ComplexResolutionCokernel.ComplexResolution.syzygyShortComplex_shortExact j D hD)
        (CechExact.Dolbeault.projectiveAlgebraicCechAcyclic_quasicoherent (n + 1) (SheafCohomology.Projective.ComplexResolutionCokernel.ComplexResolution.cokernelSheaf j D' hD'))
        (ResolutionAnalyticAcyclicity.Dolbeault.projectiveResolutionCokernel_analyticAcyclic (n + 1) j D' hD') h₁
        (projectiveResolutionFreeSheaf_comparison n j D)

theorem projectiveResolutionCokernel_comparison (n : ℕ) (j : Fin (n + 2))
    (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule (Fin (n + 2)) Γ(Foundations.Scheme.ProjectiveSpace.complexBase, ⊤))
    (hD : SheafCohomology.Projective.GradedNonnegativeSyzygy.HasNonnegativeGrading D) :
    ModuleClosure.Dolbeault.projectiveModuleComparisonIsomorphism (n + 1) (SheafCohomology.Projective.ComplexResolutionCokernel.ComplexResolution.cokernelSheaf j D hD) :=
  projectiveResolutionCokernel_comparison_of_projective_syzygy n j (n + 2) D hD
    (SheafCohomology.Projective.GradedMinimalSyzygy.iteratedMinimalGradedSyzygy_projective (n + 2) D)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.Resolution.Dolbeault
