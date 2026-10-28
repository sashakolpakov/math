import OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs
import OAI.NumberTheory.PadicHodge.GeometricComparison.Semilattice.FiniteProductPreservation

/-! # Morphism Pair Products -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairProducts.AffineMorphismPairProducts

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} [X.IsSeparated] [Y.IsSeparated] (f : X ⟶ Y)
  (n : ℕ) (U : Fin (n + 1) → MorphismPairs.AffineMorphismPairs.Charts f)
instance source_preserves : PreservesLimit (Discrete.functor U) (MorphismPairs.AffineMorphismPairs.source f) :=
  NumberTheory.PadicHodge.GeometricComparison.Semilattice.FiniteProductPreservation.SemilatticeFiniteProductPreservation.preserves (MorphismPairs.AffineMorphismPairs.source f)
    (MorphismPairs.AffineMorphismPairs.source_inf f) U
instance target_preserves : PreservesLimit (Discrete.functor U) (MorphismPairs.AffineMorphismPairs.target f) :=
  NumberTheory.PadicHodge.GeometricComparison.Semilattice.FiniteProductPreservation.SemilatticeFiniteProductPreservation.preserves (MorphismPairs.AffineMorphismPairs.target f)
    (MorphismPairs.AffineMorphismPairs.target_inf f) U

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairProducts.AffineMorphismPairProducts
