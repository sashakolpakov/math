import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameGenerators
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.LevelMap

/-! # Frame Level Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameLevelMap.IntrinsicPadicFrameLevelMap

noncomputable section

/-! Canonical prime-power reduction gives morphisms between the actual
native integral-section frames at different bounded crystalline levels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (U : X.left.Opens) (hU : IsAffineOpen U)
  (n m : ℕ) (hnm : n ≤ m)

local notation "W" => WittVector p (ZMod p)
local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X U
local notation "C" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.targetRing p X Y f U
local notation "wittMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y

local instance padic : Algebra ℤ_[p] A := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X U
local instance witt : Algebra W A := WittAlgebra.PadicWittAlgebra.algebra p A
local instance special : Algebra (ZMod p) C := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (ZMod p) Y (f ⁻¹ᵁ U)

def localMap := by
  letI := AffineFrame.IntrinsicPadicAffineFrame.source_flat p X U hU
  exact IntegralComparison.SmoothWitt.LevelMap.morphism p (ZMod p) A C
    (AffineFrame.IntrinsicPadicAffineFrame.reduction p X Y f U)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_surjective p X Y f hp U hU)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_kernel p X Y f hp U hU)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_base p X Y f hp U) n m hnm

def map :
    (IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p)
      (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
      wittMap n m hnm).obj (ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp U hU n) ⟶
        ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp U hU m :=
  (IntegralComparison.BoundedOpen.Equivalence.postcompose (ChartImage.IntrinsicPadicOpenFrame.chart p X Y f hp U hU)
    (ChartImage.IntrinsicPadicOpenFrame.chart_over_witt p X Y f hp U hU) m).map
      (localMap p X Y f hp U hU n m hnm)

theorem map_generator (a : A) :
    (IntrinsicPadicFrameLevelMap.map p X Y f hp U hU n m hnm).hom.ringMap
      (FrameGenerators.IntrinsicPadicFrameGenerators.generators p X Y f hp m U hU a) =
        FrameGenerators.IntrinsicPadicFrameGenerators.generators p X Y f hp n U hU a := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameLevelMap.IntrinsicPadicFrameLevelMap
