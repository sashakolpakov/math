import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Cup
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Descent
import OAI.AlgebraicGeometry.Cycles.Functoriality.SupportClass
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Powers

/-! # Ample Powers -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.AmplePowers.CM.Construction

noncomputable section

/-! Algebraicity of the geometric ample powers used in the middle-factor
contractions, from Lefschetz and actual cycle-class cup compatibility. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Powers.CM.Construction

theorem rational_unit_algebraic (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    AlgebraicTopology.Products.CupCohomologyAlgebra.singularCohomologyCupUnit (R := ℚ) (Betti.Scheme.schemePointSpace V.toOver) ∈
      V.geometricAlgebraicClasses 0 := by
  refine ⟨Finsupp.single (Cycles.Functoriality.Support.Construction.fullCycleSupport V) 1, ?_⟩
  rw [Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap_single, one_smul,
    Cycles.Functoriality.SupportClass.Construction.fullCycleSupport_geometricCycleClass]
  rfl

theorem fubiniStudyClass_algebraic (hlefschetz : ComplexMultiplication.CMKnownResults.CM.KnownResults.LefschetzOneOne)
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClassQ V ∈ V.geometricAlgebraicClasses 1 := by
  apply hlefschetz V
  change V.rationalCohomologyInclusion 2 (ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClassQ V) ∈ V.pureBettiSubspace 1 1
  apply (V.mem_pureBettiSubspace_iff 1 1 _).mpr
  exact ⟨ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClosedForm V,
    (Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree _).mp (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm_hasBidegree V),
    ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClassQ_comparison V⟩

theorem amplePower_algebraic (hlefschetz : ComplexMultiplication.CMKnownResults.CM.KnownResults.LefschetzOneOne)
    (h_LineBundleCycles : CycleOperations.CM.Construction.LineBundleCyclesInput) (h_ThomClass : CycleOperations.CM.Construction.ExteriorInput)
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ) :
    ComplexMultiplication.HodgeComparison.Powers.CM.Construction.fubiniStudyPowerQ V k ∈ V.geometricAlgebraicClasses k := by
  induction k with
  | zero => exact rational_unit_algebraic V
  | succ k hk =>
    exact Cup.CM.Construction.rational_cup_algebraic h_LineBundleCycles h_ThomClass V k 1
      (ComplexMultiplication.HodgeComparison.Powers.CM.Construction.fubiniStudyPowerQ V k) (ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration.CM.Construction.fubiniStudyClassQ V) hk (fubiniStudyClass_algebraic hlefschetz V)

theorem complex_amplePower_algebraic (hlefschetz : ComplexMultiplication.CMKnownResults.CM.KnownResults.LefschetzOneOne)
    (h_LineBundleCycles : CycleOperations.CM.Construction.LineBundleCyclesInput) (h_ThomClass : CycleOperations.CM.Construction.ExteriorInput)
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ) :
    V.rationalCohomologyInclusion (k + k) (ComplexMultiplication.HodgeComparison.Powers.CM.Construction.fubiniStudyPowerQ V k) ∈
      V.complexGeometricAlgebraicClasses k :=
  Descent.CM.Construction.rational_algebraic_complex_inclusion V k _ (amplePower_algebraic hlefschetz h_LineBundleCycles h_ThomClass V k)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.AmplePowers.CM.Construction
