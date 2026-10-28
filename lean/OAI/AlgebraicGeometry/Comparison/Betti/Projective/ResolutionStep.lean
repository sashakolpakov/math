import OAI.AlgebraicGeometry.Comparison.Betti.Projective.CechExact
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.ModuleClosure

/-! # Resolution Step -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.ResolutionStep.Dolbeault

noncomputable section

/-! The original comparison passes through an actual resolution step with acyclic intersections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

theorem projectiveModuleComparisonIsomorphism_resolution_step (n : ℕ)
    (S : ShortComplex (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Modules) (hS : S.ShortExact)
    (hA : CechExact.Dolbeault.projectiveAlgebraicCechAcyclic n S.X₁) (hB : ModuleCechAcyclicity.Dolbeault.projectiveAnalyticCechAcyclic n S.X₁)
    (h₁ : ModuleClosure.Dolbeault.projectiveModuleComparisonIsomorphism n S.X₁)
    (h₂ : ModuleClosure.Dolbeault.projectiveModuleComparisonIsomorphism n S.X₂) :
    ModuleClosure.Dolbeault.projectiveModuleComparisonIsomorphism n S.X₃ :=
  ModuleClosure.Dolbeault.projectiveModuleComparisonIsomorphism_cokernel n S
    (CechExact.Dolbeault.projectiveAlgebraicModuleCechFunctor_shortExact n S hS hA)
    (CechExact.Dolbeault.projectiveAnalyticModuleCechFunctor_shortExact n S hS hB) h₁ h₂

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.ResolutionStep.Dolbeault
