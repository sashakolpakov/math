import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.TypedCechPullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechHomotopy

/-! # Typed Integral One Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.TypedIntegralOneCoordinates.IntrinsicPadicGeometricTypedIntegralHOneCoordinates

noncomputable section

/-! The typed integral Cech map is the original geometric pullback
on integral Cech cohomology. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))}
  [IsProper X₁.hom] [Smooth X₁.hom] [IsProper X₂.hom] [Smooth X₂.hom]
  [X₁.left.IsSeparated] [X₂.left.IsSeparated]
  (u : X₁ ⟶ X₂) (n : ℕ)

theorem homology : TypedCechPullback.IntrinsicPadicGeometricTypedCechPullback.integralHOne p u n =
    CechHomotopy.IntrinsicPadicGeometricCechHomotopy.sourceHOneMap p u n := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.TypedIntegralOneCoordinates.IntrinsicPadicGeometricTypedIntegralHOneCoordinates
