import OAI.AlgebraicGeometry.AbelianVariety.PowerImage
import OAI.AlgebraicTopology.Cohomology.Singular.ChartLocalContractible

/-! # Connected -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Connected.CM.Construction

noncomputable section

/-! Connectedness of the actual abelian factors used for integration. -/

theorem abelian_pathConnected (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : PathConnectedSpace A.variety.analyticSpace := by
  let : ConnectedSpace A.variety.analyticSpace := AbelianVariety.PowerImage.Constructions.ExteriorCohomology.abelianPoint_connectedSpace A
  let : LocallyPathConnectedSpace A.variety.analyticSpace :=
    AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.locallyPathConnectedSpace_of_chartedSpace A.variety.analyticModel A.variety.analyticSpace
  exact PathConnectedSpace.of_locallyPathConnectedSpace

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Connected.CM.Construction
