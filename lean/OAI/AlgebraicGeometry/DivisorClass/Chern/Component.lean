import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.OpenRestriction
import OAI.AlgebraicGeometry.DivisorClass.Chern.Geometric

/-! # Component -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-!
# ChernClass: geometric divisor classes for every smooth projective line bundle

Restrict to the actual finitely many integral components, construct their
rational-section divisors, and assemble through the existing component cycle
equivalence. The resulting class uses the existing geometric cycle-class map
on the original possibly disconnected scheme, without a pure-dimension assumption.

Equality with the independently constructed logarithmic first Chern class
is not assumed here and remains the outstanding comparison theorem.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Component.Construction

/-- On an integral carrier, the component-based codimension is the usual dimension difference. -/
theorem supportCodimension_of_integral (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
    (Z : IrreducibleCloseds X.carrier) :
    X.supportCodimension Z = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.structureMap -
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.structureMap := by
  have h := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion
    (X.componentInclusion (X.supportComponent Z)) X.structureMap
  rw [X.componentInclusion_over] at h
  exact congrArg (fun d => d - Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z X.structureMap) h

/-- Identify the two existing support gradings on an integral presentation. -/
def integralSupportToVariety (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ)
    (Z : V.presentation.DimensionCycleSupport p) : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p :=
  ⟨Z.val, (supportCodimension_of_integral V.presentation Z.val).symm.trans Z.property⟩

theorem integralSupportToVariety_injective (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :
    Function.Injective (integralSupportToVariety V p) := by
  intro Z W h
  exact Subtype.ext (congrArg (fun z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p => z.val) h)

end Component.Construction

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X)

/-- The actual integral divisor on each genuine integral component. -/
def Line.Bundles.AlgebraicLineBundle.componentIntegralDivisor (C : irreducibleComponents X.carrier) :
    CycleClass.Geometric.DimensionCycles.DimensionCycleSupport (X.componentVariety C) 1 →₀ ℤ :=
  Finsupp.mapDomain (Component.Construction.integralSupportToVariety (X.componentVariety C) 1)
    (L.componentLineBundle C).rationalSectionIntegralDivisor

/-- Changing the support representation preserves every integral multiplicity. -/
theorem Line.Bundles.AlgebraicLineBundle.componentIntegralDivisor_apply (C : irreducibleComponents X.carrier)
    (Z : (X.componentVariety C).presentation.DimensionCycleSupport 1) :
    L.componentIntegralDivisor C (Component.Construction.integralSupportToVariety (X.componentVariety C) 1 Z) =
      (L.componentLineBundle C).rationalSectionIntegralDivisor Z :=
  Finsupp.mapDomain_apply_of_injective (Component.Construction.integralSupportToVariety_injective (X.componentVariety C) 1) _ Z

/-- Rationalize precisely the integer multiplicities of the component divisor. -/
def Line.Bundles.AlgebraicLineBundle.componentRationalDivisor (C : irreducibleComponents X.carrier) :
    CycleClass.Geometric.DimensionCycles.RationalDimensionCycle (X.componentVariety C) 1 :=
  Finsupp.mapRange (fun n : ℤ => (n : ℚ)) (Int.cast_zero) (L.componentIntegralDivisor C)

/-- A finite divisor cycle on the original scheme, assembled from its actual component divisors. -/
def Line.Bundles.AlgebraicLineBundle.algebraicDivisorCycle : X.RationalDimensionCycle 1 :=
  (X.componentDimensionCycleEquiv 1).symm L.componentRationalDivisor

theorem Line.Bundles.AlgebraicLineBundle.algebraicDivisorCycle_components :
    X.componentDimensionCycleEquiv 1 L.algebraicDivisorCycle = L.componentRationalDivisor :=
  (X.componentDimensionCycleEquiv 1).apply_symm_apply _

/-- The geometric class of the actual line-bundle divisor, on any smooth projective scheme. -/
def Line.Bundles.AlgebraicLineBundle.algebraicDivisorClass : X.rationalCohomology 2 :=
  X.geometricCycleClassMap 1 L.algebraicDivisorCycle

theorem Line.Bundles.AlgebraicLineBundle.algebraicDivisorClass_eq :
    L.algebraicDivisorClass = X.geometricCycleClassMap 1 L.algebraicDivisorCycle := rfl

/-- Each component of this class is the existing geometric class of that component's actual divisor. -/
theorem Line.Bundles.AlgebraicLineBundle.algebraicDivisorClass_components (C : irreducibleComponents X.carrier) :
    X.componentBettiEquiv (ModuleCat.of ℚ ℚ) 2 L.algebraicDivisorClass C =
      (X.componentVariety C).geometricCycleClassMap 1 (L.componentRationalDivisor C) := by
  have h := X.componentBettiEquiv_geometricCycleClassMap 1 L.algebraicDivisorCycle C
  rw [L.algebraicDivisorCycle_components] at h
  exact h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
