import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameLevelRingCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.AlgebraicRingHomCoordinates

/-! # Reduction Level Square -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReductionLevelSquare.IntrinsicPadicReductionLevelSquare

noncomputable section

/-! Original integral-to-frame reductions commute with the actual native
bounded-level maps as natural transformations of algebra diagrams. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n m : ℕ) (hnm : n ≤ m) (I : X.left.affineOpens)

local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X I.val
local notation "αn" => NatTrans.app (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientFrameNaturalIso.IntrinsicPadicQuotientRingMap.transformation p X Y f hp n) (op I)
local notation "αm" => NatTrans.app (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientFrameNaturalIso.IntrinsicPadicQuotientRingMap.transformation p X Y f hp m) (op I)
local notation "β" => NatTrans.app (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameLevelComplexMap.IntrinsicPadicFrameLevelComplexMap.rings p X Y f hp n m hnm) (op I)

theorem composite_coordinates : (αm ≫ β).hom.toRingHom = (β).hom.toRingHom.comp (αm).hom.toRingHom :=
  AlgebraicRingHomCoordinates.CommAlgebraicRingHomCoordinates.comp αm β

theorem coefficient_coordinates : (β).hom.toRingHom.comp (αm).hom.toRingHom =
    (IntegralComparison.PD.TruncationTransition.map A (Ideal.span {(p : A)}) n m hnm).comp
      (Ideal.Quotient.mk ((Ideal.span {(p : A)}) ^ (m + 1))) :=
  congrArg₂ (fun (b : A ⧸ (Ideal.span {(p : A)}) ^ (m + 1) →+* A ⧸ (Ideal.span {(p : A)}) ^ (n + 1))
    (a : A →+* A ⧸ (Ideal.span {(p : A)}) ^ (m + 1)) => b.comp a)
    (FrameLevelRingCoordinates.IntrinsicPadicFrameLevelRingCoordinates.level p X Y f hp I n m hnm)
    (FrameLevelRingCoordinates.IntrinsicPadicFrameLevelRingCoordinates.reduction p X Y f hp I m)

theorem ringHom : (αm ≫ β).hom.toRingHom = (αn).hom.toRingHom :=
  (composite_coordinates p X Y f hp n m hnm I).trans
    ((coefficient_coordinates p X Y f hp n m hnm I).trans
      ((IntegralComparison.PD.TruncationTransition.map_quotient A (Ideal.span {(p : A)}) n m hnm).trans
        (FrameLevelRingCoordinates.IntrinsicPadicFrameLevelRingCoordinates.reduction p X Y f hp I n).symm))

theorem component : αm ≫ β = αn := AlgebraicRingHomExt.CommAlgebraicRingHomExt.eq _ _ (ringHom p X Y f hp n m hnm I)

theorem natural : QuotientFrameNaturalIso.IntrinsicPadicQuotientRingMap.transformation p X Y f hp m ≫
    FrameLevelComplexMap.IntrinsicPadicFrameLevelComplexMap.rings p X Y f hp n m hnm =
      QuotientFrameNaturalIso.IntrinsicPadicQuotientRingMap.transformation p X Y f hp n := by
  apply NatTrans.ext
  funext I
  exact component p X Y f hp n m hnm I.unop

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReductionLevelSquare.IntrinsicPadicReductionLevelSquare
