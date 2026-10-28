import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonomorphicOpenTo

/-! # Monomorphic Open Chart Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The Cartesian chart square of monomorphic open-chart gluing,
expressed in the category of schemes over the original base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}} {M : Over S} {J : Type u}
    (C : MonomorphicOpenTo.MonomorphicOpenCharts M J)

theorem MonomorphicOpenTo.MonomorphicOpenCharts.chartOver_isPullback (j : J) :
    IsPullback (C.chartOver j) (C.chartMap j) C.inclusion (C.baseMap j) := by
  apply IsPullback.of_map_of_faithful (Over.forget S)
  exact C.chart_isPullback j

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
