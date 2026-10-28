import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.Counting
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Construction
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Construction
import OAI.AlgebraicGeometry.PELModuli.CMPoints.Primes

/-! # Established Ordinary -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EstablishedOrdinary.CM.Ordinary

noncomputable section

/-! Full original ordinary inputs, including all canonical quotient,
Frobenius-kernel, native reduction, excluded-field and prime clauses.
The suppliers preserve the complete consumer propositions and universes. -/

universe u v

theorem native_reduction : Neighbor.Counting.CM.NeighborCountingInput :=
  Isogenies.NeighborCounting.Construction.ordinary_neighbor_reduction_multiplicities

theorem ordinary_operators : Isogenies.NeighborCounting.Prerequisites.FullFrobeniusKernelInput :=
  AbelianScheme.FrobeniusKernel.Construction.ordinary_kernel_operators_and_frobenius

theorem ordinary_primes : AbelianScheme.FrobeniusKernel.CMPoints.Construction.CMPointsInput := by
  intro E K _ _ _ _ _ _ _ M hM I _ fields _ _ excluded bound
  exact PELModuli.CMPoints.Primes.Core.exists_completely_split_prime_dense_ordinary
    E K M hM fields excluded bound

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EstablishedOrdinary.CM.Ordinary
