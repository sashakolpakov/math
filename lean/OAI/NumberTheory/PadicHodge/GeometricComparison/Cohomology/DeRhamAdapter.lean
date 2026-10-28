import OAI.NumberTheory.PadicHodge.GeometricComparison.DeRham.FiltrationPullback
import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo

/-! # De Rham Adapter -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.DeRhamAdapter.DeRham

noncomputable section

/-! The repaired Cohomology pullback specializes to the same constructed de Rham pullback as GeometricComparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {R : Type} [CommRing R] {X Y : Over (Spec (CommRingCat.of R))}

theorem pullback_eq_Cohomology (f : X ⟶ Y) (n : ℕ) :
    DeRham.Int.pullback f n = AlgebraicGeometry.Crystalline.Cohomology.DeRhamPullbackTo.DeRhamPullback.pullback f n := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.DeRhamAdapter.DeRham
