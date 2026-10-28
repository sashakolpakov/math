import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientFrameNaturalIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameGenerators

/-! # Quotient Reduction Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientReductionCoordinates.IntrinsicPadicQuotientReductionCoordinates

noncomputable section

/-! Original native quotient reduction is the canonical quotient generator
in the actual global frame ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X
local notation "B" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.rings p X Y f hp n

theorem component (U : X.left.affineOpens) (x : AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X U.val) :
    (QuotientFrameNaturalIso.IntrinsicPadicQuotientRingMap.transformation p X Y f hp n).app (op U) x =
      FrameGenerators.IntrinsicPadicFrameGenerators.generators p X Y f hp n U.val U.property x := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientReductionCoordinates.IntrinsicPadicQuotientReductionCoordinates
