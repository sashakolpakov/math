import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameLevelSquare
import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.RingSquare
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.LevelRingCoordinates

/-! # Open Frame Level Square -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.OpenFrameLevelSquare.IntrinsicPadicOpenFrameLevelSquare

noncomputable section

/-! The original global native frame morphisms commute with level reduction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (U V : X.left.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ V)
  (n m : ℕ) (hnm : n ≤ m)

local notation "W" => WittVector p (ZMod p)
local notation "incl" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p)
  (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
  (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) n m hnm

def first := (incl).map (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp U V hU hV hUV n) ≫
  FrameLevelMap.IntrinsicPadicFrameLevelMap.map p X Y f hp V hV n m hnm

def second := FrameLevelMap.IntrinsicPadicFrameLevelMap.map p X Y f hp U hU n m hnm ≫
  PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp U V hU hV hUV m

theorem first_coordinates : (first p X Y f hp U V hU hV hUV n m hnm).hom.ringMap.toRingHom =
    (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp U V hU hV hUV n).hom.ringMap.toRingHom.comp
      (FrameLevelMap.IntrinsicPadicFrameLevelMap.map p X Y f hp V hV n m hnm).hom.ringMap.toRingHom :=
  (BoundedFrame.RingSquare.BoundedFrameRingSquare.comp_ringHom
    ((incl).map (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp U V hU hV hUV n))
    (FrameLevelMap.IntrinsicPadicFrameLevelMap.map p X Y f hp V hV n m hnm)).trans
      (congrArg
        (fun a : (ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp V hV n).obj.ring →+*
          (ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp U hU n).obj.ring =>
          a.comp (FrameLevelMap.IntrinsicPadicFrameLevelMap.map p X Y f hp V hV n m hnm).hom.ringMap.toRingHom)
        (Bounded.LevelRingCoordinates.BoundedLevelRingCoordinates.ringHom (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) n m hnm
          (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp U V hU hV hUV n)))

theorem second_coordinates : (second p X Y f hp U V hU hV hUV n m hnm).hom.ringMap.toRingHom =
    (FrameLevelMap.IntrinsicPadicFrameLevelMap.map p X Y f hp U hU n m hnm).hom.ringMap.toRingHom.comp
      (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp U V hU hV hUV m).hom.ringMap.toRingHom :=
  BoundedFrame.RingSquare.BoundedFrameRingSquare.comp_ringHom (FrameLevelMap.IntrinsicPadicFrameLevelMap.map p X Y f hp U hU n m hnm)
    (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp U V hU hV hUV m)

theorem ringHom : (first p X Y f hp U V hU hV hUV n m hnm).hom.ringMap.toRingHom =
    (second p X Y f hp U V hU hV hUV n m hnm).hom.ringMap.toRingHom :=
  (first_coordinates p X Y f hp U V hU hV hUV n m hnm).trans
    ((FrameLevelSquare.IntrinsicPadicFrameLevelRawSquare.ringHom p X Y f hp U V hU hV hUV n m hnm).trans
      (second_coordinates p X Y f hp U V hU hV hUV n m hnm).symm)

theorem square : first p X Y f hp U V hU hV hUV n m hnm = second p X Y f hp U V hU hV hUV n m hnm :=
  BoundedFrame.RingSquare.BoundedFrameRingSquare.ringHom (ringHom p X Y f hp U V hU hV hUV n m hnm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.OpenFrameLevelSquare.IntrinsicPadicOpenFrameLevelSquare
