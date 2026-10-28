import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LineBundles
import OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemeGroup

/-! # Class Comparison -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.ClassComparison

/-! Actual PoincareBundle tensor classes agree with multiplication in the intrinsic scheme Picard group. -/

open _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.LineBundles OAI.AlgebraicGeometry.Picard.Homomorphisms.SchemeGroup.Construction

/-- The comparison preserves tensor products of the same actual locally free sheaves. -/
theorem classEquiv_tensor {X : Scheme.{u}} (q r : Line.Bundles.LineBundleClass X) :
    Line.Comparison.Bundle.classEquiv X (LineBundles.tensorClass q r) = Line.Comparison.Bundle.classEquiv X q * Line.Comparison.Bundle.classEquiv X r := by
  induction q using Quotient.inductionOn with
  | _ L =>
    induction r using Quotient.inductionOn with
    | _ M => rfl

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Tensor.ClassComparison
