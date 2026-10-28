import OAI.AlgebraicGeometry.DivisorClass.Chern.Components
import OAI.AlgebraicGeometry.DivisorClass.Chern.Thom

/-! # Component Thom Comparison -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-!
# ChernClass: the original divisor comparison on arbitrary presentations

Actual Chern restriction and the proved integral comparison identify every
component with the Thom class of precisely its original divisor. Empty,
disconnected, and mixed-dimension presentations use the same construction.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X)

/-- The component's preexisting divisor has exactly the cycle in the
proved supported Thom sum; rationalization commutes with the support map. -/
theorem Line.Bundles.AlgebraicLineBundle.componentRationalDivisor_eq_ThomCycle (C : irreducibleComponents X.carrier) :
    L.componentRationalDivisor C = (L.componentLineBundle C).rationalSectionDivisorThomCycle := by
  rw [(L.componentLineBundle C).rationalSectionDivisorThomCycle_eq_actual]
  change Finsupp.mapRange (fun n : ℤ => (n : ℚ)) Int.cast_zero
      (Finsupp.mapDomain (Component.Construction.integralSupportToVariety (X.componentVariety C) 1)
        (L.componentLineBundle C).rationalSectionIntegralDivisor) =
    Finsupp.mapDomain (Component.Construction.integralSupportToVariety (X.componentVariety C) 1)
      (Finsupp.mapRange (fun n : ℤ => (n : ℚ)) Int.cast_zero
        (L.componentLineBundle C).rationalSectionIntegralDivisor)
  exact (Finsupp.mapDomain_mapRange _ _ _ _ Int.cast_add).symm

/-- Every actual component of the original first Chern class is its original
divisor's Thom class with the proved common primitive orientation coefficient. -/
theorem Line.Bundles.AlgebraicLineBundle.firstChernClassQ_components_eq_divisorThom (C : irreducibleComponents X.carrier) :
    X.componentBettiEquiv (ModuleCat.of ℚ ℚ) 2 (First.firstChernClassQ X L) C =
      NormalWinding.normalWindingCoefficient •
        (X.componentVariety C).rationalCycleClass 1 (L.componentRationalDivisor C) := by
  rw [L.firstChernClassQ_components, L.componentRationalDivisor_eq_ThomCycle]
  have h := (L.componentLineBundle C).firstChernClassQ_eq_actualDivisorThom
  rw [← (L.componentLineBundle C).rationalSectionDivisorThomCycle_eq_actual] at h
  exact h

/-- Actual reconstruction from the component restrictions gives the class
on the whole original scheme, without a common dimension hypothesis. -/
theorem Line.Bundles.AlgebraicLineBundle.firstChernClassQ_eq_componentDivisorThom :
    First.firstChernClassQ X L = (X.componentBettiEquiv (ModuleCat.of ℚ ℚ) 2).symm
      (fun C => NormalWinding.normalWindingCoefficient •
        (X.componentVariety C).rationalCycleClass 1 (L.componentRationalDivisor C)) := by
  apply (X.componentBettiEquiv (ModuleCat.of ℚ ℚ) 2).injective
  rw [LinearEquiv.apply_symm_apply]
  funext C
  exact L.firstChernClassQ_components_eq_divisorThom C

/-- The full requested equality is now equivalent to the independent
geometric comparison on precisely the original component divisors. -/
theorem Line.Bundles.AlgebraicLineBundle.firstChernClassQ_eq_algebraicDivisorClass_iff_Thom_geometric :
    First.firstChernClassQ X L = L.algebraicDivisorClass ↔
      ∀ C : irreducibleComponents X.carrier,
        NormalWinding.normalWindingCoefficient •
          (X.componentVariety C).rationalCycleClass 1 (L.componentRationalDivisor C) =
        (X.componentVariety C).geometricCycleClassMap 1 (L.componentRationalDivisor C) := by
  rw [L.firstChernClassQ_eq_algebraicDivisorClass_iff_components]
  constructor <;> intro h C
  · rw [← L.firstChernClassQ_components_eq_divisorThom C, L.firstChernClassQ_components]
    exact h C
  · rw [← L.firstChernClassQ_components C, L.firstChernClassQ_components_eq_divisorThom]
    exact h C

/-- The original geometric comparison is complete when the actual assembled
divisor vanishes, on any smooth projective presentation. -/
theorem Line.Bundles.AlgebraicLineBundle.firstChernClassQ_eq_algebraicDivisorClass_of_divisorCycle_zero
    (hL : L.algebraicDivisorCycle = 0) : First.firstChernClassQ X L = L.algebraicDivisorClass := by
  apply L.firstChernClassQ_eq_algebraicDivisorClass_iff_Thom_geometric.mpr
  intro C
  have hC := congrFun L.algebraicDivisorCycle_components C
  rw [hL, map_zero] at hC
  change 0 = L.componentRationalDivisor C at hC
  rw [← hC, map_zero, map_zero, smul_zero]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
