import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameLevelComplexMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientFrameNaturalIso

/-! # Frame Level Ring Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameLevelRingCoordinates.IntrinsicPadicFrameLevelRingCoordinates

noncomputable section

/-! Actual ambient algebra level maps and integral reductions retain
the canonical native prime-power ring homomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (I : X.left.affineOpens)

local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X I.val

theorem reduction (n : ℕ) :
    ((QuotientFrameNaturalIso.IntrinsicPadicQuotientRingMap.transformation p X Y f hp n).app (op I)).hom.toRingHom =
      Ideal.Quotient.mk ((Ideal.span {(p : A)}) ^ (n + 1)) := rfl

theorem level_raw (n m : ℕ) (hnm : n ≤ m) :
    ((FrameLevelComplexMap.IntrinsicPadicFrameLevelComplexMap.rings p X Y f hp n m hnm).app (op I)).hom.toRingHom =
      (FrameLevelMap.IntrinsicPadicFrameLevelMap.map p X Y f hp I.val I.property n m hnm).hom.ringMap.toRingHom := rfl

theorem level (n m : ℕ) (hnm : n ≤ m) :
    ((FrameLevelComplexMap.IntrinsicPadicFrameLevelComplexMap.rings p X Y f hp n m hnm).app (op I)).hom.toRingHom =
      IntegralComparison.PD.TruncationTransition.map A (Ideal.span {(p : A)}) n m hnm :=
  (level_raw p X Y f hp I n m hnm).trans
    (FrameLevelSquare.IntrinsicPadicFrameLevelRingNaturality.level_ringHom p X Y f hp I.val I.property n m hnm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameLevelRingCoordinates.IntrinsicPadicFrameLevelRingCoordinates
