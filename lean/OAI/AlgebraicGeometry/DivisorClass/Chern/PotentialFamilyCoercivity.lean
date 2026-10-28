import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.PositiveCurvature
import OAI.AlgebraicGeometry.DivisorClass.Chern.UniformCurvatureCoercivity
import OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.SmoothDolbeault

/-! # Potential Family Coercivity -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.PotentialFamilyCoercivity

noncomputable section

/-! A proved uniform curvature lower bound for real potentials gives one actual twist threshold for all of their native smooth Dolbeault solvers. -/

open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem positiveHolomorphicTwistMetric_potential_family_coercive (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    {ι : Type*} (f : ι → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0)
    (hf : ∀ t, ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm (f t) = f t) (B : ℝ)
    (hB : ∀ t (x : V.analyticSpace) (v : TangentSpace 𝓘(ℝ, V.analyticModel) x), v ≠ 0 →
      -B * (ComplexMultiplication.HodgeComparison.IntrinsicProjectiveCharts.CM.Construction.varietyFubiniStudyForm V x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re ≤
        ((Complex.I • Projective.ScalarPotential.globalScalarCurvature (f t)) x ![v, Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentSMul x Complex.I v]).re) :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ∀ t : ι,
      ((Holomorphic.PositiveCurvature.positiveHolomorphicTwistMetric V u h n).withPotential (f t)).smoothDolbeaultOneCoercive V := by
  let threshold := UniformCurvatureCoercivity.projective_exists_uniform_curvature_coercivity V
  let twists := Holomorphic.PositiveCurvature.positiveHolomorphicTwistMetric_projective_lower_bound V u h (threshold.choose + B)
  refine ⟨twists.choose, twists.choose_spec.1, ?_⟩
  intro n hn t
  exact threshold.choose_spec.2 _ _
    ((Holomorphic.PositiveCurvature.positiveHolomorphicTwistMetric V u h n).withPotential_projective_lower_bound V (f t) (hf t)
      threshold.choose B (fun x v hv => (twists.choose_spec.2 n hn x v hv).le) (hB t))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.PotentialFamilyCoercivity
