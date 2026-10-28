import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Additive
import OAI.AlgebraicGeometry.DivisorClass.Chern.IntegralSheafLattice

/-! # Lifting -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Lifting

noncomputable section

/-! Vanishing of the actual holomorphic obstruction yields an original holomorphic Chern class after scaling. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M] [CompactSpace M] [NormalSpace M]
  [MetrizableSpace M] [StronglyLocallyContractibleSpace M] [LocallyPathConnectedSpace M]

theorem exists_holomorphicFirstChernClassQ_multiple
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) 2)
    (ha : Rational.HolomorphicPeriod.rationalHolomorphicObstruction E M (Rational.BettiCechSheafComparison.rationalBettiCechSheafEquiv (TopCat.of M) 1 a) = 0) :
    ∃ N : ℕ, 0 < N ∧ ∃ u : Connecting.holomorphicUnitCohomology E M,
      Singular.holomorphicFirstChernClassQ E M u = N • a := by
  obtain ⟨N, hN, u, hu⟩ := IntegralSheafLattice.exists_holomorphicUnitClass_rational_multiple E M
    (Rational.BettiCechSheafComparison.rationalBettiCechSheafEquiv (TopCat.of M) 1 a) ha
  refine ⟨N, hN, u, ?_⟩
  apply (Rational.BettiCechSheafComparison.rationalBettiCechSheafEquiv (TopCat.of M) 1).injective
  rw [Additive.holomorphicFirstChernClassQ_connecting, map_nsmul]
  exact hu

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Lifting
