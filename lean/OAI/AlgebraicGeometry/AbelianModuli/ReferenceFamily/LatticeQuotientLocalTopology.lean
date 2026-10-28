import Mathlib.Topology.Algebra.OpenSubgroup
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularPeriodEquiv
import OAI.AlgebraicTopology.Cohomology.Singular.ChartLocalContractible
import Mathlib.Geometry.Manifold.Instances.Quotient
import Mathlib.Topology.Metrizable.Urysohn

/-! # Lattice Quotient Local Topology -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeQuotientLocalTopology

noncomputable section

/-! Local manifold topology and metrizability of the actual quotient by a
discrete lattice, for use in singular-to-sheaf comparison. -/

open _root_.TopologicalSpace

open OAI.AlgebraicTopology.Cohomology.Singular.ChartLocalContractible

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (Λ : Submodule ℤ V) [DiscreteTopology Λ]

@[instance_reducible]
def latticeQuotientChartedSpace : ChartedSpace V (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) :=
  (SingularPeriodEquiv.SingularPeriodComparison.projection_covering Λ).isLocalHomeomorph.chartedSpace
    QuotientAddGroup.mk_surjective

theorem latticeQuotient_stronglyLocallyContractible : StronglyLocallyContractibleSpace (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) := by
  let := latticeQuotientChartedSpace Λ
  exact AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.stronglyLocallyContractibleSpace_of_chartedSpace V (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)

theorem latticeQuotient_locallyPathConnected : LocallyPathConnectedSpace (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) := by
  let := latticeQuotientChartedSpace Λ
  exact AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.locallyPathConnectedSpace_of_chartedSpace V (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ)

omit [NormedSpace ℝ V] in
theorem latticeQuotient_metrizable [SecondCountableTopology V] : MetrizableSpace (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base Λ) := by
  have : IsClosed (Λ.toAddSubgroup : Set V) := AddSubgroup.isClosed_of_discreteTopology
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeQuotientLocalTopology
