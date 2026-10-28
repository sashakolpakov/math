import OAI.AlgebraicGeometry.ComplexMultiplication.BundledAbelianBridge
import OAI.AlgebraicGeometry.Betti.SmoothDimension
import OAI.AlgebraicGeometry.Smooth.Equidimensional

/-! # Manifold Dimension Bridge -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ManifoldDimensionBridge

noncomputable section

/-! # The two actual complex manifold dimensions agree

The older atlas uses the function-field differential dimension; the original
atlas uses the scheme dimension. Their equality follows from the uniqueness
of the relative dimension of the same smooth integral complex scheme.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

/-- Both actual analytic atlases have the same complex dimension, without a CM hypothesis. -/
theorem functionFieldDifferentialDimension_eq_originalDimension :
    Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom = Topology.Dimension.Basic.TopologicalSpace.dim X.left := by
  let := Betti.SmoothDimension.Realization.smoothOfFunctionFieldDimension X.hom
  exact (AlgebraicGeometry.Smooth.Equidimensional.SmoothOfRelativeDimension.dim_eq X.hom
    (Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom)).symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ManifoldDimensionBridge
