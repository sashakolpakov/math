import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameLevelMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.RingSquare
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameLevelSquare
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.OpenFrameLevelSquare

/-! # Frame Level Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameLevelNaturality.IntrinsicPadicFrameLevelNaturality

noncomputable section

/-! Native prime-power frame reductions commute with all affine-open
restriction maps and form a natural transformation between levels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n m : ℕ) (hnm : n ≤ m)

local notation "W" => WittVector p (ZMod p)
local notation "wittMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "incl" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p)
  (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) wittMap n m hnm
local notation "frame" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor.IntrinsicPadicFrameFunctor.functor p X Y f hp

theorem natural {U V : X.left.affineOpens} (α : U ⟶ V) :
    (incl).map ((frame n).map α) ≫ FrameLevelMap.IntrinsicPadicFrameLevelMap.map p X Y f hp V.val V.property n m hnm =
      FrameLevelMap.IntrinsicPadicFrameLevelMap.map p X Y f hp U.val U.property n m hnm ≫ (frame m).map α :=
  OpenFrameLevelSquare.IntrinsicPadicOpenFrameLevelSquare.square p X Y f hp U.val V.val U.property V.property (leOfHom α) n m hnm

def transformation : frame n ⋙ incl ⟶ frame m where
  app U := FrameLevelMap.IntrinsicPadicFrameLevelMap.map p X Y f hp U.val U.property n m hnm
  naturality _ _ α := natural p X Y f hp n m hnm α

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameLevelNaturality.IntrinsicPadicFrameLevelNaturality
