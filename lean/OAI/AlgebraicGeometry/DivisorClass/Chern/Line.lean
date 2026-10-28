import OAI.AlgebraicGeometry.DivisorClass.Chern.ThomGeometricCycle
import OAI.AlgebraicGeometry.DivisorClass.Chern.NormalizedComparison

/-! # Line -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line

noncomputable section

/-!
# ChernClass: compatibility of the actual first Chern class with the original divisor

The logarithmic Chern construction and its proved independence are unchanged.
The geometric class is the existing fundamental-trace construction applied to
the same bundle's original rational-section divisor. The equality follows from
the original supported Thom comparison, the proved complex orientation, and
the actual global compact Thom trace; no comparison hypothesis is assumed.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Bundles.AlgebraicLineBundle X)

/-- The actual logarithmic first Chern class equals the independently defined
geometric class of this same bundle's original rational-section divisor. -/
theorem Bundles.AlgebraicLineBundle.firstChernClassQ_eq_algebraicDivisorClass :
    First.firstChernClassQ X L = L.algebraicDivisorClass := by
  apply L.firstChernClassQ_eq_algebraicDivisorClass_iff_Thom_geometric.mpr
  intro C
  rw [NormalGeometricTrace.normalWindingCoefficient_eq_one, one_smul, ThomGeometricCycle.rationalCycleClassMap_eq_geometric]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line
