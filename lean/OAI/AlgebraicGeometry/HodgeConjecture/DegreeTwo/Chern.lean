import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ChernGeometric
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Presentation

/-! # Chern -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Chern.Constructions

noncomputable section

/-!
# DegreeTwo: the full conditional degree-two Hodge clause

ChernClassInput is the complete Lefschetz proposition from Statements/ChernClass.lean at. Its first Chern
classes are the original algebraic-line-bundle classes. The independently
proved Thom/geometric comparison supplies the geometric cycle representative;
that comparison is not an additional hypothesis.
-/

open _root_.CategoryTheory

/-- The full reviewed ChernClass proposition, retained as an explicit input. -/
def ChernClassInput : Prop :=
  ∀ (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (a : X.rationalCohomology 2),
    X.IsRationalHodgeClass 1 a →
      a ∈ Submodule.span ℚ (Set.range (DivisorClass.Chern.First.firstChernClassQ X))

/-- Every rational degree-two Hodge class has an actual geometric cycle
representative, conditional only on the full reviewed Lefschetz input. -/
theorem degree_two_algebraicity (hChernClass : ChernClassInput)
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (α : V.rationalCohomology 2)
    (hα : V.IsRationalHodgeClass 1 α) :
    ∃ z : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle V 1, V.geometricCycleClassMap 1 z = α :=
  ChernGeometric.Constructions.firstChern_span_is_geometric V α
    (hChernClass V.presentation α (Presentation.Constructions.presentation_isRationalHodgeClass V 1 α hα))

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Chern.Constructions
