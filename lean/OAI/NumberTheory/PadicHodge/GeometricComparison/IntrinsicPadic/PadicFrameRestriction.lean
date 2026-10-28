import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameRestrictionData
import OAI.NumberTheory.PadicHodge.GeometricComparison.Smooth.WittFrameMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FramePostcomposition

/-! # Padic Frame Restriction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicFrameRestriction.IntrinsicPadicFrameRestriction

noncomputable section

/-! Restriction between actual affine integral opens induces the original
global bounded crystalline frame map, with the actual quotient-ring formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameRestrictionData.IntrinsicPadicFrameRestrictionData

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (U V : X.left.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ V)

local notation "W" => WittVector p (ZMod p)
local notation "AU" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X U
local notation "AV" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X V
local notation "CU" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.targetRing p X Y f U
local notation "CV" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.targetRing p X Y f V
local notation "g" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameRestrictionData.IntrinsicPadicFrameRestrictionData.geometricMap p X Y f U V hUV
local notation "hg" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameRestrictionData.IntrinsicPadicFrameRestrictionData.geometric_over_witt p X Y f hp U V hU hV hUV

local instance padicU : Algebra ℤ_[p] AU := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X U
local instance padicV : Algebra ℤ_[p] AV := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X V
local instance wittU : Algebra W AU := WittAlgebra.PadicWittAlgebra.algebra p AU
local instance wittV : Algebra W AV := WittAlgebra.PadicWittAlgebra.algebra p AV
local instance specialU : Algebra (ZMod p) CU := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (ZMod p) Y (f ⁻¹ᵁ U)
local instance specialV : Algebra (ZMod p) CV := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (ZMod p) Y (f ⁻¹ᵁ V)

def localMap (n : ℕ) :
    (IntegralComparison.BoundedOpen.Equivalence.postcompose g hg n).obj (AffineFrame.IntrinsicPadicAffineFrame.frame p X Y f hp U hU n) ⟶
      AffineFrame.IntrinsicPadicAffineFrame.frame p X Y f hp V hV n := by
  letI : Module.Flat W AU := AffineFrame.IntrinsicPadicAffineFrame.source_flat p X U hU
  letI : Module.Flat W AV := AffineFrame.IntrinsicPadicAffineFrame.source_flat p X V hV
  exact GeometricComparison.Smooth.WittFrameMap.SmoothWittFrameGeometricMap.boundedMorphism p (ZMod p) AV AU CV CU
    (AffineFrame.IntrinsicPadicAffineFrame.reduction p X Y f V)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_surjective p X Y f hp V hV)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_kernel p X Y f hp V hV)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_base p X Y f hp V)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction p X Y f U)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_surjective p X Y f hp U hU)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_kernel p X Y f hp U hU)
    (AffineFrame.IntrinsicPadicAffineFrame.reduction_base p X Y f hp U)
    (FrameRestrictionData.IntrinsicPadicFrameRestrictionData.integralMap p X U V hUV) (FrameRestrictionData.IntrinsicPadicFrameRestrictionData.specialMap p X Y f U V hUV).toRingHom
    (FrameRestrictionData.IntrinsicPadicFrameRestrictionData.reduction_square p X Y f U V hUV) g hg rfl n

def map (n : ℕ) : ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp U hU n ⟶
    ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp V hV n :=
  Crystalline.FramePostcomposition.CrystallineFramePostcomposition.map g (ChartImage.IntrinsicPadicOpenFrame.chart p X Y f hp V hV)
    (ChartImage.IntrinsicPadicOpenFrame.chart p X Y f hp U hU) hg
    (ChartImage.IntrinsicPadicOpenFrame.chart_over_witt p X Y f hp V hV)
    (ChartImage.IntrinsicPadicOpenFrame.chart_over_witt p X Y f hp U hU)
    (FrameRestrictionData.IntrinsicPadicFrameRestrictionData.chart_square p X Y f hp U V hU hV hUV) n (localMap p X Y f hp U V hU hV hUV n)

theorem map_ringMap (n : ℕ) : (IntrinsicPadicFrameRestriction.map p X Y f hp U V hU hV hUV n).hom.ringMap =
    (localMap p X Y f hp U V hU hV hUV n).hom.ringMap :=
  Crystalline.FramePostcomposition.CrystallineFramePostcomposition.ringMap g (ChartImage.IntrinsicPadicOpenFrame.chart p X Y f hp V hV)
    (ChartImage.IntrinsicPadicOpenFrame.chart p X Y f hp U hU) hg
    (ChartImage.IntrinsicPadicOpenFrame.chart_over_witt p X Y f hp V hV)
    (ChartImage.IntrinsicPadicOpenFrame.chart_over_witt p X Y f hp U hU)
    (FrameRestrictionData.IntrinsicPadicFrameRestrictionData.chart_square p X Y f hp U V hU hV hUV) n (localMap p X Y f hp U V hU hV hUV n)

theorem map_mk (n : ℕ) (a : AV) :
    (IntrinsicPadicFrameRestriction.map p X Y f hp U V hU hV hUV n).hom.ringMap
      (Ideal.Quotient.mk ((Ideal.span {(p : AV)}) ^ (n + 1)) a) =
    Ideal.Quotient.mk ((Ideal.span {(p : AU)}) ^ (n + 1)) (FrameRestrictionData.IntrinsicPadicFrameRestrictionData.integralMap p X U V hUV a) := by
  rw [map_ringMap]
  rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PadicFrameRestriction.IntrinsicPadicFrameRestriction
