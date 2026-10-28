import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Smooth

/-! # Vector Representative AE -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorRepresentativeAE.Constructions

noncomputable section

/-! Equality of a bounded continuous vector representative and an actual
L² field as distributions implies almost-everywhere equality of their values. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap ContDiff
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Smooth.CM.Construction

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem vectorBoundedFunctionDistribution_eq_lp_ae (f : BoundedContinuousFunction E F)
    (u : Lp F 2 (volume : Measure E))
    (h : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevInv.CM.Construction.boundedFunctionDistribution f = (u : 𝓢'(E, F))) :
    (f : E → F) =ᵐ[volume] u := by
  apply ae_eq_of_integral_contDiff_smul_eq f.continuous.locallyIntegrable
    (Lp.memLp u |>.locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2))
  intro g hg hgc
  have hc : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hs : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  have heq := congrArg (fun T : 𝓢'(E, F) => T (hc.toSchwartzMap hs)) h
  rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevInv.CM.Construction.boundedFunctionDistribution_apply, Lp.toTemperedDistribution_apply] at heq
  change (∫ x, (g x : ℂ) • f x) = ∫ x, (g x : ℂ) • u x at heq
  simpa only [Complex.coe_smul] using heq

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorRepresentativeAE.Constructions
