import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs
import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.FiniteProductPreservation

/-! # Map Pair Products -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairProducts.AffineMapPairProducts

noncomputable section

/-! Both projections from compatible affine pairs preserve the actual
nonempty tuple products used in the original Cech construction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {X Y : Scheme.{0}} [X.IsSeparated] [Y.IsSeparated] (f : X ⟶ Y)
  (n : ℕ) (U : Fin (n + 1) → MapPairs.AffineMapPairs.Charts f)

instance source_preserves : PreservesLimit (Discrete.functor U) (MapPairs.AffineMapPairs.source f) :=
  Semilattice.FiniteProductPreservation.SemilatticeFiniteProductPreservation.preserves (MapPairs.AffineMapPairs.source f)
    (MapPairs.AffineMapPairs.source_inf f) U

instance target_preserves : PreservesLimit (Discrete.functor U) (MapPairs.AffineMapPairs.target f) :=
  Semilattice.FiniteProductPreservation.SemilatticeFiniteProductPreservation.preserves (MapPairs.AffineMapPairs.target f)
    (MapPairs.AffineMapPairs.target_inf f) U

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairProducts.AffineMapPairProducts
