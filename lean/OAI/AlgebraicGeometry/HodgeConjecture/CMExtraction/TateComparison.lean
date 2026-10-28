import OAI.RepresentationTheory.Theta.Geometric.TateComparison
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparison

/-! # Tate Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparison.Intrinsic

/-! The two committed TateComparison interfaces state the same full proposition. -/

theorem native_full_c47_input (h : HeckeCycles.TateComparison.CM.TateComparisonInput) :
    RepresentationTheory.Theta.Geometric.TateComparison.TateComparisonInput := h

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.TateComparison.Intrinsic
