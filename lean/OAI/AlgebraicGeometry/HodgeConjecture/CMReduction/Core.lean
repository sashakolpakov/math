import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Established

/-! # Core -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Core

open OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Established.CM

theorem cm_hodge : ComplexMultiplication.CMCore.CM.cmHodgeClaim := by
  exact FourFactorSwitches.CM.Construction.four_factor_switches_imply_cm Established.scalarTrace Established.connectivity
    Established.properPushforward Established.geometricPullback Established.exteriorProduct Established.oppositePairing
    Established.realization Established.fullness Established.lefschetz Established.exterior Established.cycles Established.switches

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Core
