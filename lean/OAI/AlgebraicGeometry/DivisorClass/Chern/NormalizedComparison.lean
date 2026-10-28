import OAI.AlgebraicGeometry.DivisorClass.Chern.ComponentThomComparison
import OAI.AlgebraicGeometry.DivisorClass.Chern.NormalGeometricTrace

/-! # Normalized Comparison -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-!
# ChernClass: the divisor comparison with the repaired complex normalization

`SphereCover.standardSphereOverlapEquiv` now uses the actual ordered
equator coordinates. The integral positive-circle calculation proves its
normal winding coefficient is one. Consequently the original Chern class
equals the Thom class of the same original rational-section divisor,
including all components of a disconnected presentation.

The independent fundamental-trace definition of `geometricCycleClassMap`
still requires its Thom comparison. That comparison is not assumed here.

## Impact on ThomClass

The public sphere, local homology, fundamental-class, and geometric-cycle
constructor types are unchanged. Their primitive orientation has changed
from unspecified real equator bases to ordered real coordinates. ThomClass's
algebraic intersections, local Tor multiplicities, rational equivalences,
and exterior cycle construction are unchanged. Its geometric class values
inherit the corrected orientation through the ambient and regular-locus
fundamental classes. The existing normalization theorem states the precise
dependence: source orientation divided by ambient orientation. Thus ThomClass's
product equalities require coherent product normalization, not merely an
arbitrary independent primitive sign in each complex dimension.

`Check.py` rebuilds every affected base module and rechecks the existing
ThomClass constructors and finite-cycle reductions. ThomClass's two target statements
retain their original proofs pending its separate compatibility proof stage.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem NormalizedComparison.normalWindingCompactClass_geometricTrace_one :
    AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace 1 (M := Fin 1 → ℂ) NormalGeometricTrace.normalWindingCompactClass = 1 := by
  rw [NormalGeometricTrace.normalWindingCompactClass_geometricTrace, NormalGeometricTrace.normalWindingCoefficient_eq_one]

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X)

theorem Line.Bundles.AlgebraicLineBundle.rationalSectionChernRelativeClass_eq_divisorThom_positive [IsIntegral X.carrier] :
    L.rationalSectionChernRelativeClass = L.rationalSectionDivisorThomClass := by
  rw [L.rationalSectionChernRelativeClass_eq_actualDivisorThom,
    NormalGeometricTrace.normalWindingCoefficient_eq_one, one_smul]

theorem Line.Bundles.AlgebraicLineBundle.firstChernClassQ_eq_divisorThom_positive [IsIntegral X.carrier] :
    First.firstChernClassQ X L = (SupportedDivisorSum.Construction.integralPresentationVariety X).rationalCycleClass 1
      L.rationalSectionDivisorThomCycle := by
  rw [L.firstChernClassQ_eq_actualDivisorThom, ← L.rationalSectionDivisorThomCycle_eq_actual,
    NormalGeometricTrace.normalWindingCoefficient_eq_one, one_smul]

theorem Line.Bundles.AlgebraicLineBundle.firstChernClassQ_components_eq_divisorThom_positive (C : irreducibleComponents X.carrier) :
    X.componentBettiEquiv (ModuleCat.of ℚ ℚ) 2 (First.firstChernClassQ X L) C =
      (X.componentVariety C).rationalCycleClass 1 (L.componentRationalDivisor C) := by
  rw [L.firstChernClassQ_components_eq_divisorThom, NormalGeometricTrace.normalWindingCoefficient_eq_one, one_smul]

theorem Line.Bundles.AlgebraicLineBundle.firstChernClassQ_eq_componentDivisorThom_positive :
    First.firstChernClassQ X L = (X.componentBettiEquiv (ModuleCat.of ℚ ℚ) 2).symm
      (fun C => (X.componentVariety C).rationalCycleClass 1 (L.componentRationalDivisor C)) := by
  apply (X.componentBettiEquiv (ModuleCat.of ℚ ℚ) 2).injective
  rw [LinearEquiv.apply_symm_apply]
  funext C
  exact L.firstChernClassQ_components_eq_divisorThom_positive C

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
