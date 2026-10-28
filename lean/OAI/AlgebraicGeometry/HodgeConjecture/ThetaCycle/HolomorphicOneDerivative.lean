import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallForms
import OAI.Analysis.DifferentialForms.Manifold.DolbeaultCoefficientType

/-! # Holomorphic One Derivative -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.HolomorphicOneDerivative.CM

noncomputable section

/-! ThetaCycle: the literal holomorphic theta covector has a pure (2,0)
exterior derivative, computed with the actual real derivative. -/

open Filter
open scoped Classical _root_.Manifold ContDiff _root_.Topology
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

section
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def complexCovectorOverComplex : (E →L[ℂ] ℂ) →L[ℂ] Analysis.DifferentialForms.Manifold.Basic.FormValue E 1 where
  toFun := Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector E
  map_add' _ _ := by ext v; rfl
  map_smul' _ _ := by ext v; rfl
  cont := (BallForms.CM.complexCovectorCLM E).continuous

theorem holomorphic_one_extDeriv_pure {f : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1} {x : E}
    (hf : DifferentiableAt ℂ f x)
    (hp : ∀ᶠ y in 𝓝 x, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 0 (f y)) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 2 0 (extDeriv f x) := by
  have hd : fderiv ℝ f x = (fderiv ℂ f x).restrictScalars ℝ :=
    (hf.hasFDerivAt.restrictScalars ℝ).fderiv
  intro c v
  have h := Analysis.DifferentialForms.Manifold.DolbeaultCoefficientType.alternatizeUncurryFin_scaling (fderiv ℝ f x) (c : ℂ) (c : ℂ)
    (Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 1 0 c) (fun u => ?_)
    (fun u w => Analysis.DifferentialForms.Manifold.DolbeaultCoefficientType.fderiv_hasBidegree (hf.restrictScalars ℝ) hp u c w) v
  · simpa only [extDeriv, Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_one, pow_zero, mul_one, pow_two] using! h
  · rw [hd]
    change fderiv ℂ f x ((c : ℂ) • u) = (c : ℂ) • fderiv ℂ f x u
    exact map_smul (fderiv ℂ f x) (c : ℂ) u
end

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Gal(K/ℚ) → Bool}

theorem source_ball_one_derivative_pure (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)
    (φ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places)) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart B.Domain 2 0 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (BallForms.CM.sourceBallOneForm K L φ)).val := by
  intro e he z hz
  have hzB : z ∈ B.domain := by rwa [Analysis.DifferentialForms.Manifold.OpenEquivalence.openChart_target e he] at hz
  have hlocal : (BallForms.CM.sourceBallOneForm K L φ).val.inChart e =ᶠ[𝓝 z]
      (fun y => Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector HeckeCycles.GeometricSource.CM.BallChart (Projection.CM.sourceThetaCovector K L φ y)) := by
    filter_upwards [B.domain_isOpen.mem_nhds hzB] with y hy
    exact BallForms.CM.source_ball_one_inChart K L φ e he hy
  rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_inChart _ e he hz, hlocal.extDeriv_eq]
  apply holomorphic_one_extDeriv_pure HeckeCycles.GeometricSource.CM.BallChart
  · exact (complexCovectorOverComplex HeckeCycles.GeometricSource.CM.BallChart).differentiableAt.comp z
      ((Projection.CM.source_theta_covector_holomorphic K L φ z hzB).differentiableAt
        (B.domain_isOpen.mem_nhds hzB))
  · exact Eventually.of_forall (fun _ => Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector_hasBidegree HeckeCycles.GeometricSource.CM.BallChart _)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.HolomorphicOneDerivative.CM
