import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.BaseChangeCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.SectionBase
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence

/-! # Chart Image -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ChartImage.IntrinsicPadicOpenFrame

/-! The actual affine integral-section frames lie on the global crystalline
site through the original special-fiber affine-open charts. -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (U : X.left.Opens) (hU : IsAffineOpen U)

local notation "C" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AffineFrame.IntrinsicPadicAffineFrame.targetRing p X Y f U
local instance specialAlgebra : Algebra (ZMod p) C := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (ZMod p) Y (f ⁻¹ᵁ U)

include hp hU in
omit [Smooth X.hom] in
theorem special_affine : IsAffineOpen (f ⁻¹ᵁ U) :=
  Affine.BaseChangeCover.AffineBaseChangeCover.affine PadicInt.toZMod X Y f hp U hU

def chart : (IntegralComparison.Crystalline.Presentation.affineScheme (ZMod p) C).left ⟶ Y.left := (special_affine p X Y f hp U hU).fromSpec

instance chart_open : IsOpenImmersion (chart p X Y f hp U hU) :=
  IsAffineOpen.isOpenImmersion_fromSpec (special_affine p X Y f hp U hU)

omit [Smooth X.hom] in
theorem chart_over : chart p X Y f hp U hU ≫ Y.hom = (IntegralComparison.Crystalline.Presentation.affineScheme (ZMod p) C).hom :=
  IntegralComparison.AffineOpen.SectionBase.overBase (ZMod p) Y (f ⁻¹ᵁ U) (special_affine p X Y f hp U hU)

omit [Smooth X.hom] in
theorem chart_over_witt : chart p X Y f hp U hU ≫ IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y =
    IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) (IntegralComparison.Crystalline.Presentation.affineScheme (ZMod p) C) := by
  change chart p X Y f hp U hU ≫ (Y.hom ≫ _) = (IntegralComparison.Crystalline.Presentation.affineScheme (ZMod p) C).hom ≫ _
  rw [← Category.assoc, chart_over]

def frame (n : ℕ) :=
  (IntegralComparison.BoundedOpen.Equivalence.postcompose (chart p X Y f hp U hU)
    (chart_over_witt p X Y f hp U hU) n).obj (AffineFrame.IntrinsicPadicAffineFrame.frame p X Y f hp U hU n)

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ChartImage.IntrinsicPadicOpenFrame

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ChartImage.IntrinsicPadicChartImage

/-! The actual native special-fiber chart has exactly the original
inverse-image open as its open image. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p])))
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (U : X.left.Opens) (hU : IsAffineOpen U)

theorem opensRange : (IntrinsicPadicOpenFrame.chart p X Y f hp U hU).opensRange = f ⁻¹ᵁ U := by
  apply TopologicalSpace.Opens.ext
  exact IsAffineOpen.range_fromSpec (IntrinsicPadicOpenFrame.special_affine p X Y f hp U hU)

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ChartImage.IntrinsicPadicChartImage

end

end OAI
