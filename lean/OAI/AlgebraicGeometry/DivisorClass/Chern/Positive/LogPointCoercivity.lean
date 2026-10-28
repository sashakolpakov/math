import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.LogGlobalLowerBound
import OAI.AlgebraicGeometry.DivisorClass.Chern.PotentialFamilyCoercivity

/-! # Log Point Coercivity -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.LogPointCoercivity

noncomputable section

/-! A single actual holomorphic twist threshold supplies native coercive smooth solvers for every sufficiently small regularization of the constructed logarithmic point metric. -/

open Filter Set
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (η : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
  (hs : tsupport η ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
  (x : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hηx : η =ᶠ[𝓝 x] fun _ => 1) (m : ℕ)

include hηx

theorem positiveHolomorphicTwistMetric_log_point_coercive :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ 1 →
      ((Holomorphic.PositiveCurvature.positiveHolomorphicTwistMetric V u h n).withPotential
        (Projective.LogPointPotential.projectiveLogPointPotential V e he η hη hc hs x m ε hε)).smoothDolbeaultOneCoercive V := by
  let family := fun t : Ioc (0 : ℝ) 1 => Projective.LogPointPotential.projectiveLogPointPotential V e he η hη hc hs x m t.val t.property.1
  let bound := Projective.LogGlobalLowerBound.projectiveLogPointPotential_global_lower_bound V e he η hη hc hs x hηx m
  let solvers := PotentialFamilyCoercivity.positiveHolomorphicTwistMetric_potential_family_coercive V h family
    (fun t => Projective.LogPointPotential.projectiveLogPointPotential_real V e he η hη hc hs x m t.val t.property.1) bound.choose
    (fun t => bound.choose_spec.2 t.val t.property.1 t.property.2)
  exact ⟨solvers.choose, solvers.choose_spec.1,
    fun n hn ε hε hε1 => solvers.choose_spec.2 n hn ⟨ε, hε, hε1⟩⟩

theorem positiveHolomorphicTwistMetric_log_point_dolbeault :
    ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n → ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ 1 →
      ((Holomorphic.PositiveCurvature.positiveHolomorphicTwistMetric V u h n).withPotential
        (Projective.LogPointPotential.projectiveLogPointPotential V e he η hη hc hs x m ε hε)).hasBoundedSmoothDolbeaultPrimitives V := by
  let solvers := positiveHolomorphicTwistMetric_log_point_coercive V h e he η hη hc hs x hηx m
  exact ⟨solvers.choose, solvers.choose_spec.1, fun n hn ε hε hε1 =>
    HolomorphicMetric.Data.HolomorphicLineMetricData.hasBoundedSmoothDolbeaultPrimitives_of_coercive V _
      (solvers.choose_spec.2 n hn ε hε hε1)⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.LogPointCoercivity
