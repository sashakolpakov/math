import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameLevelComplexMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralInjective
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SectionChange

/-! # Frame Source Level Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameSourceLevelMap.IntrinsicPadicFrameSourceLevelMap

noncomputable section

/-! Native frame-level de Rham maps retain the original large coefficient
functor used by the frame-to-section comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n m : ℕ) (hnm : n ≤ m)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))

def transformation : FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.source p X Y f hp m ⟶
    FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.source p X Y f hp n :=
  Functor.whiskerRight (FrameLevelComplexMap.IntrinsicPadicFrameLevelComplexMap.pd p X Y f hp n m hnm)
    ((IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.coefficients p).mapHomologicalComplex (.up ℕ))

omit [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem component (U : X.left.affineOpens) : (transformation p X Y f hp n m hnm).app (op U) =
    ((ModuleCat.uliftFunctor.{2, 1} R).mapHomologicalComplex (.up ℕ)).map
      (IntegralComparison.BoundedFrame.SectionChange.frameMap
        (FrameLevelMap.IntrinsicPadicFrameLevelMap.map p X Y f hp U.val U.property n m hnm)) := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameSourceLevelMap.IntrinsicPadicFrameSourceLevelMap
