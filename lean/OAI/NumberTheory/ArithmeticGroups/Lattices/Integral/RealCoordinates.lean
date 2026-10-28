import OAI.NumberTheory.ArithmeticGroups.Lattices.DiagonalActionSquareBound
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Instances.Int

/-! # Real Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.RealCoordinates.Construction

noncomputable section

/-! Integral coordinate vectors are closed and discrete, have a unit
gap in each nonzero coordinate, and meet bounded sets in finitely many points. -/

open Set

def integralRealCoordinates (ι : Type*) : Set (ι → ℝ) :=
  Set.range (fun z : ι → ℤ => fun i => (z i : ℝ))

theorem integralRealCoordinates_closed (ι : Type*) : IsClosed (integralRealCoordinates ι) :=
  (Topology.IsClosedEmbedding.piMap (fun _ : ι => Int.isClosedEmbedding_coe_real)).isClosed_range

theorem integralRealCoordinates_discrete (ι : Type*) [Finite ι] :
    IsDiscrete (integralRealCoordinates ι) :=
  (Topology.IsClosedEmbedding.piMap (fun _ : ι => Int.isClosedEmbedding_coe_real)).isEmbedding.isInducing.isDiscrete_range

theorem integralRealCoordinates_gap {ι : Type*} (x : ι → ℝ)
    (hx : x ∈ integralRealCoordinates ι) (i : ι) : x i = 0 ∨ 1 ≤ |x i| := by
  obtain ⟨z, rfl⟩ := hx
  change (z i : ℝ) = 0 ∨ 1 ≤ |(z i : ℝ)|
  by_cases hz : z i = 0
  · exact Or.inl (by rw [hz, Int.cast_zero])
  · right
    exact_mod_cast (Int.one_le_abs hz)

theorem integral_coordinates_finite_of_bounded
    {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V] [Fintype ι]
    (e : V ≃L[ℝ] (ι → ℝ)) (S : Set V) (R : ℝ) (hR : ∀ x ∈ S, ‖x‖ ≤ R)
    (hint : ∀ x ∈ S, e x ∈ integralRealCoordinates ι) : S.Finite := by
  have hclosed : IsClosed (e ⁻¹' integralRealCoordinates ι) :=
    (integralRealCoordinates_closed ι).preimage e.continuous
  have hdiscrete : IsDiscrete (e ⁻¹' integralRealCoordinates ι) :=
    (integralRealCoordinates_discrete ι).preimage e.continuous.continuousOn e.injective
  apply (Metric.finite_isBounded_inter_isClosed hdiscrete
    (Metric.isBounded_closedBall (x := (0 : V)) (r := R)) hclosed).subset
  intro x hx
  exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hR x hx, hint x hx⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Integral.RealCoordinates.Construction
