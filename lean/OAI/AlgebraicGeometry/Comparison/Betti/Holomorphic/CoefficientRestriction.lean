import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.Restrictions
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FormFrames
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.HolomorphicPullback
import OAI.AlgebraicGeometry.Comparison.Betti.Open.ManifoldRestriction

/-! # Coefficient Restriction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.CoefficientRestriction

noncomputable section

/-! The coefficient description commutes with the actual holomorphic pullback along open inclusion. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {U V : Opens E} {n : ℕ}

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

def holomorphicCoefficientRestrict (h : V ≤ U) :
    CoefficientMem.holomorphicOpenCoefficients U n →ₗ[ℂ] CoefficientMem.holomorphicOpenCoefficients V n where
  toFun a := ⟨fun x => a.val (Opens.inclusion h x), by
    constructor
    · intro x
      exact a.property.1 (Opens.inclusion h x)
    · apply (a.property.2.mono h).congr
      intro x hx
      rw [Analysis.DifferentialForms.Manifold.OpenD.openFormExtension_apply V _ ⟨x, hx⟩, Analysis.DifferentialForms.Manifold.OpenD.openFormExtension_apply U _ ⟨x, h hx⟩]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem holomorphicCoefficientsToForm_restrict (h : V ≤ U)
    (a : CoefficientMem.holomorphicOpenCoefficients U n) :
    CoefficientMem.holomorphicCoefficientsToForm V n (holomorphicCoefficientRestrict h a) =
      HolomorphicPullback.pullback (Opens.inclusion h) (contMDiff_inclusion (I := 𝓘(ℂ, E)) h) n
        (CoefficientMem.holomorphicCoefficientsToForm U n a) := by
  apply HolomorphicPullback.inclusion_injective n
  rw [CoefficientMem.holomorphicCoefficientsToForm_inclusion, HolomorphicPullback.pullback_inclusion,
    CoefficientMem.holomorphicCoefficientsToForm_inclusion]
  exact Open.ManifoldRestriction.Holomorphic.smoothOpenManifoldEquiv_restrict h (CoefficientMem.holomorphicCoefficientsSmoothForm a)

variable [FiniteDimensional ℂ E]

theorem formToHolomorphicCoefficients_pullback (h : V ≤ U) (a : DeRhamComplex.forms E U n) :
    CoefficientMem.formToHolomorphicCoefficients V n
      (HolomorphicPullback.pullback (Opens.inclusion h) (contMDiff_inclusion (I := 𝓘(ℂ, E)) h) n a) =
        holomorphicCoefficientRestrict h (CoefficientMem.formToHolomorphicCoefficients U n a) := by
  apply (CoefficientMem.holomorphicCoefficientsEquivForms V n).injective
  change CoefficientMem.holomorphicCoefficientsToForm V n (CoefficientMem.formToHolomorphicCoefficients V n _) =
    CoefficientMem.holomorphicCoefficientsToForm V n (holomorphicCoefficientRestrict h _)
  rw [CoefficientMem.coefficientsToForm_formToCoefficients, holomorphicCoefficientsToForm_restrict,
    CoefficientMem.coefficientsToForm_formToCoefficients]

theorem holomorphicPureSectionEquiv_restrict (h : V ≤ U)
    (a : CoefficientMem.holomorphicOpenCoefficients U n) :
    FunctionPure.holomorphicPureSectionEquiv V n (holomorphicCoefficientRestrict h a) =
      Restrictions.holomorphicSectionRestrict h (FunctionPure.holomorphicPureSectionEquiv U n a) := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.CoefficientRestriction
