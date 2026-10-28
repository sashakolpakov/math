import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AnalyticRealization
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.AlgebraicIntegrationTransport
import OAI.AlgebraicGeometry.ComplexMultiplication.CMKnownResults

/-! # Intrinsic Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.IntrinsicComparison.CM.Abelian

noncomputable section

/-! # CMAbelianVariety: the genuine rational H¹ comparison on the algebraic period model -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff TensorProduct
open OAI.AlgebraicGeometry.ComplexMultiplication.CMKnownResults.CM

variable {U ι : Type} [AddCommGroup U] [Module ℚ U]
  [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ U)
  (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (P : ComplexMultiplication.CM.Polarization.WeightOnePolarization H)
  (hRiemannProjectivity : ProjectiveTorusData.CM.Abelian.RiemannProjectivityInput) (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

local notation "D" => OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.ProjectiveTorusData.CM.Abelian.ProjectivePeriodData.ofHodgeStructure b H P hRiemannProjectivity

def rationalComparison
    (e : (D).periodTorus ≃ₘ⟮𝓘(ℂ, (D).space), 𝓘(ℂ, V.analyticModel)⟯ V.analyticSpace) :
    U ≃ₗ[ℚ] V.rationalCohomology 1 :=
  (RationalPeriods.CM.Abelian.polarizedRationalBettiEquiv b H P hRiemannProjectivity).trans (Geometry.ComplexTorus.RiemannProjectivity.BettiTransportTop.Constructions.BettiTransport.iso ℚ e.toHomeomorph 1).toLinearEquiv.symm

theorem rational_pullback
    (e : (D).periodTorus ≃ₘ⟮𝓘(ℂ, (D).space), 𝓘(ℂ, V.analyticModel)⟯ V.analyticSpace) (a : U) :
    (Geometry.ComplexTorus.RiemannProjectivity.BettiTransportTop.Constructions.BettiTransport.iso ℚ e.toHomeomorph 1).hom (rationalComparison b H P hRiemannProjectivity V e a) =
      RationalPeriods.CM.Abelian.polarizedRationalBettiEquiv b H P hRiemannProjectivity a :=
  (Geometry.ComplexTorus.RiemannProjectivity.BettiTransportTop.Constructions.BettiTransport.iso ℚ e.toHomeomorph 1).toLinearEquiv.apply_symm_apply _

theorem complex_pullback
    (e : (D).periodTorus ≃ₘ⟮𝓘(ℂ, (D).space), 𝓘(ℂ, V.analyticModel)⟯ V.analyticSpace)
    (x : ComplexMultiplication.WeightOne.CM.Complexification U) :
    (Geometry.ComplexTorus.RiemannProjectivity.BettiTransportTop.Constructions.BettiTransport.iso ℂ e.toHomeomorph 1).hom
      (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (TopCat.of V.analyticSpace) 1
        ((rationalComparison b H P hRiemannProjectivity V e).toLinearMap.baseChange ℂ x)) =
      AnalyticRealization.CM.Abelian.GenericAnalyticRealization.complexComparison b H P hRiemannProjectivity x := by
  refine (Geometry.ComplexTorus.RiemannProjectivity.BettiTransportTop.Constructions.BettiTransport.complexification_naturality e.toHomeomorph 1
    ((rationalComparison b H P hRiemannProjectivity V e).toLinearMap.baseChange ℂ x)).trans ?_
  change ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (TopCat.of (D).periodTorus) 1
    (((Geometry.ComplexTorus.RiemannProjectivity.BettiTransportTop.Constructions.BettiTransport.iso ℚ e.toHomeomorph 1).hom.hom.baseChange ℂ)
      ((rationalComparison b H P hRiemannProjectivity V e).toLinearMap.baseChange ℂ x)) =
    ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (TopCat.of (D).periodTorus) 1
      ((RationalPeriods.CM.Abelian.polarizedRationalBettiEquiv b H P hRiemannProjectivity).toLinearMap.baseChange ℂ x)
  congr 1
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add]
    exact (((Geometry.ComplexTorus.RiemannProjectivity.BettiTransportTop.Constructions.BettiTransport.iso ℚ e.toHomeomorph 1).hom.hom.baseChange ℂ).map_add _ _).trans
      (congrArg₂ (· + ·) hx hy)
  | tmul c a =>
    simp only [LinearMap.baseChange_tmul]
    exact congrArg (fun y => c ⊗ₜ[ℚ] y) (rational_pullback b H P hRiemannProjectivity V e a)

theorem holomorphic
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : (D).periodTorus ≃ₘ⟮𝓘(ℂ, (D).space), 𝓘(ℂ, A.variety.analyticModel)⟯ A.variety.analyticSpace)
    (x : ComplexMultiplication.WeightOne.CM.Complexification U) :
    (rationalComparison b H P hRiemannProjectivity A.variety e).toLinearMap.baseChange ℂ x ∈ A.h1Holomorphic ↔
      x ∈ H.holomorphic := by
  change A.h1ScalarExtension ((rationalComparison b H P hRiemannProjectivity A.variety e).toLinearMap.baseChange ℂ x) ∈
    A.variety.pureBettiSubspace 1 0 ↔ _
  rw [AlgebraicIntegrationTransport.CM.Abelian.Algebraization.IntrinsicPureComparison.pureBetti_iff D A.variety e 1 0]
  change (∃ a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms ((D).space) (D).periodTorus 1,
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree ((D).space) (D).periodTorus 1 0 a.val ∧
    AlgebraicBetti.CM.Abelian.Algebraization.Betti.deRhamBettiEquiv D 1 (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass ((D).space) (D).periodTorus 1 a) =
      (Geometry.ComplexTorus.RiemannProjectivity.BettiTransportTop.Constructions.BettiTransport.iso ℂ e.toHomeomorph 1).hom
        (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (TopCat.of A.variety.analyticSpace) 1
          ((rationalComparison b H P hRiemannProjectivity A.variety e).toLinearMap.baseChange ℂ x))) ↔ _
  rw [complex_pullback]
  exact AnalyticRealization.CM.Abelian.GenericAnalyticRealization.holomorphic_comparison b H P hRiemannProjectivity x

theorem antiholomorphic
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (e : (D).periodTorus ≃ₘ⟮𝓘(ℂ, (D).space), 𝓘(ℂ, A.variety.analyticModel)⟯ A.variety.analyticSpace)
    (x : ComplexMultiplication.WeightOne.CM.Complexification U) :
    (rationalComparison b H P hRiemannProjectivity A.variety e).toLinearMap.baseChange ℂ x ∈ A.h1Antiholomorphic ↔
      x ∈ H.antiholomorphic := by
  change A.h1ScalarExtension ((rationalComparison b H P hRiemannProjectivity A.variety e).toLinearMap.baseChange ℂ x) ∈
    A.variety.pureBettiSubspace 0 1 ↔ _
  rw [AlgebraicIntegrationTransport.CM.Abelian.Algebraization.IntrinsicPureComparison.pureBetti_iff D A.variety e 0 1]
  change (∃ a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms ((D).space) (D).periodTorus 1,
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree ((D).space) (D).periodTorus 0 1 a.val ∧
    AlgebraicBetti.CM.Abelian.Algebraization.Betti.deRhamBettiEquiv D 1 (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass ((D).space) (D).periodTorus 1 a) =
      (Geometry.ComplexTorus.RiemannProjectivity.BettiTransportTop.Constructions.BettiTransport.iso ℂ e.toHomeomorph 1).hom
        (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (TopCat.of A.variety.analyticSpace) 1
          ((rationalComparison b H P hRiemannProjectivity A.variety e).toLinearMap.baseChange ℂ x))) ↔ _
  rw [complex_pullback]
  exact AnalyticRealization.CM.Abelian.GenericAnalyticRealization.antiholomorphic_comparison b H P hRiemannProjectivity x

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.IntrinsicComparison.CM.Abelian
