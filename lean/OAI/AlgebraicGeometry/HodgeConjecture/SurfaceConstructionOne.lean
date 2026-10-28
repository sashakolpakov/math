import OAI.AlgebraicGeometry.HodgeConjecture.Coefficients
import OAI.AlgebraicGeometry.DivisorClass.Chern.First

/-! # Surface Construction One -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.SurfaceConstructionOne.CM

noncomputable section

/-! Full current prerequisite interfaces at the final SurfaceConstruction boundary.
DegreeTwo's committed degree-two statement is itself conditional on the full
ChernClass Lefschetz proposition; both propositions are retained explicitly here. -/

/-- The full Lefschetz statement in Statements/ChernClass.lean. -/
def LefschetzOneOneInput : Prop :=
  ∀ (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (a : X.rationalCohomology 2),
    X.IsRationalHodgeClass 1 a →
      a ∈ Submodule.span ℚ (Set.range (DivisorClass.Chern.First.firstChernClassQ X))

/-- The full current DegreeTwo degree-two statement, including its ChernClass input. -/
def DegreeTwoAlgebraicityInput : Prop :=
  ∀ (_hE09 : LefschetzOneOneInput)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (a : X.rationalCohomology 2),
    X.IsRationalHodgeClass 1 a →
      ∃ z : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle X 1, X.geometricCycleClassMap 1 z = a

theorem degreeTwoAlgebraicity_of_inputs
    (hDegreeTwo : DegreeTwoAlgebraicityInput) (hChernClass : LefschetzOneOneInput) :
    Coefficients.CM.SurfaceConstruction.DegreeTwoAlgebraicity := hDegreeTwo hChernClass

end

end OAI.AlgebraicGeometry.HodgeConjecture.SurfaceConstructionOne.CM
