import OAI.AlgebraicGeometry.DivisorClass.Chern.Line
import OAI.AlgebraicGeometry.DivisorClass.Chern.ComponentProjectiveSpan
import OAI.AlgebraicGeometry.Betti.ProjectivePresentationCohomology
import OAI.AlgebraicGeometry.DivisorClass.Chern.Iso
import OAI.AlgebraicGeometry.DivisorClass.Chern.Component
import OAI.AlgebraicGeometry.DivisorClass.Chern.WindingComparison
import OAI.AlgebraicGeometry.DivisorClass.Chern.ConcreteResidue
import OAI.AlgebraicGeometry.DivisorClass.Chern.SupportModel
import OAI.AlgebraicGeometry.DivisorClass.Chern.SupportedDivisorSum
import OAI.AlgebraicGeometry.DivisorClass.Chern.Intrinsic.DivisorModel
import OAI.AlgebraicGeometry.DivisorClass.Chern.ComponentThomComparison
import OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.WindingNormalization
import OAI.AlgebraicGeometry.DivisorClass.Chern.CircleEquatorOrientation
import OAI.AlgebraicGeometry.DivisorClass.Chern.NormalGeometricTrace
import OAI.AlgebraicGeometry.DivisorClass.Chern.OrientationCondition
import OAI.AlgebraicGeometry.DivisorClass.Chern.NormalizedComparison
import OAI.AlgebraicGeometry.DivisorClass.Chern.LocalProductCoefficientOne

/-! # Lefschetz -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Lefschetz

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- ChernClass: every rational degree-two Hodge class is a finite
 rational linear combination of algebraic first Chern classes. -/
theorem lefschetz_one_one
    (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (a : X.rationalCohomology 2)
    (ha : X.IsRationalHodgeClass 1 a) :
    a ∈ Submodule.span ℚ (Set.range (First.firstChernClassQ X)) := by
  exact ComponentProjectiveSpan.originalPresentation_lefschetz_one_one X a ha

end OAI.AlgebraicGeometry.DivisorClass.Chern.Lefschetz
