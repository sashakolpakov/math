import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConstructionCapstone
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.HodgeComparisonCapstone
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EstablishedTorsionQuotient
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Mem
import OAI.Analysis.HodgeTheory.Decomposition.Constructions

/-! # Established Geometric -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EstablishedGeometric.CM

noncomputable section

/-! Complete Albanese, Hodge comparison, Hodge decomposition and finite
etale parameter inputs. HodgeDecomposition retains every degree and filtration clause. -/

universe u

theorem albanese : PELModuli.IntegralModel.Albanese.ConstructionInput :=
  PELModuli.IntegralModel.ConstructionCapstone.provedConstructionInput

theorem albanese_hodge_comparison : PELModuli.IntegralModel.AlbaneseCohomology.HodgeComparisonInput :=
  PELModuli.IntegralModel.HodgeComparisonCapstone.provedHodgeComparisonInput

theorem hodge_decomposition : CMExtraction.Mem.HodgeDecompositionInput :=
  Analysis.HodgeTheory.Decomposition.Constructions.hodge_decomposition_and_filtration

theorem torsion_parameters : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput :=
  Isogenies.NeighborCounting.EstablishedTorsionQuotient.fullTorsionQuotientInput

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EstablishedGeometric.CM
