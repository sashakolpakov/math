import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ChartImage

/-! # Frame Restriction Data -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameRestrictionData.IntrinsicPadicFrameRestrictionData

noncomputable section

/-! The actual restriction maps on integral and special-fiber affine sections
give compatible Witt algebra maps and the original affine chart square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p])))
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (U V : X.left.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ V)

local notation "W" => WittVector p (ZMod p)
local notation "AU" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X U
local notation "AV" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X V
local notation "CU" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.targetRing p X Y f U
local notation "CV" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.targetRing p X Y f V

local instance padicU : Algebra ℤ_[p] AU := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X U
local instance padicV : Algebra ℤ_[p] AV := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X V
local instance wittU : Algebra W AU := WittAlgebra.PadicWittAlgebra.algebra p AU
local instance wittV : Algebra W AV := WittAlgebra.PadicWittAlgebra.algebra p AV
local instance specialU : Algebra (ZMod p) CU := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (ZMod p) Y (f ⁻¹ᵁ U)
local instance specialV : Algebra (ZMod p) CV := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (ZMod p) Y (f ⁻¹ᵁ V)

def integralMap : AV →ₐ[W] AU :=
  { (X.left.presheaf.map (homOfLE hUV).op).hom with
    commutes' := fun w =>
      ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras ℤ_[p] X).map (homOfLE hUV).op).hom.commutes ((WittVector.equiv p) w) }

def specialMap : CV →ₐ[ZMod p] CU :=
  ((AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebras (ZMod p) Y).map
    (((TopologicalSpace.Opens.map f.base).map (homOfLE hUV)).op)).hom

theorem reduction_square (a : AV) :
    AffineFrame.IntrinsicPadicAffineFrame.reduction p X Y f U (integralMap p X U V hUV a) =
      specialMap p X Y f U V hUV (AffineFrame.IntrinsicPadicAffineFrame.reduction p X Y f V a) :=
  ConcreteCategory.congr_hom (f.naturality (homOfLE hUV).op) a

def geometricMap : (IntegralComparison.Crystalline.Presentation.affineScheme (ZMod p) CU).left ⟶ (IntegralComparison.Crystalline.Presentation.affineScheme (ZMod p) CV).left :=
  Spec.map (CommRingCat.ofHom (specialMap p X Y f U V hUV).toRingHom)

include hp hU hV in
theorem chart_square : geometricMap p X Y f U V hUV ≫ ChartImage.IntrinsicPadicOpenFrame.chart p X Y f hp V hV =
    ChartImage.IntrinsicPadicOpenFrame.chart p X Y f hp U hU :=
  (ChartImage.IntrinsicPadicOpenFrame.special_affine p X Y f hp V hV).map_fromSpec
    (ChartImage.IntrinsicPadicOpenFrame.special_affine p X Y f hp U hU)
    (((TopologicalSpace.Opens.map f.base).map (homOfLE hUV)).op)

include hp hU hV in
theorem geometric_over_witt : geometricMap p X Y f U V hUV ≫
    IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) (IntegralComparison.Crystalline.Presentation.affineScheme (ZMod p) CV) =
      IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) (IntegralComparison.Crystalline.Presentation.affineScheme (ZMod p) CU) := by
  rw [← ChartImage.IntrinsicPadicOpenFrame.chart_over_witt p X Y f hp V hV, ← Category.assoc,
    chart_square p X Y f hp U V hU hV hUV, ChartImage.IntrinsicPadicOpenFrame.chart_over_witt]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameRestrictionData.IntrinsicPadicFrameRestrictionData
