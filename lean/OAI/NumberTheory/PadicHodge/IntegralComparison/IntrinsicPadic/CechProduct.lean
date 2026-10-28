import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSheafResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.DiagramCechProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.DiagramProduct

/-! # Cech Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.CechProduct.Intrinsic

noncomputable section

/-! The actual p-adic-model Čech presheaf resolution carries its
native PD wedge/Alexander–Whitney product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p])))
  [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p)))) (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)
local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechPresheafResolution.IntrinsicPadicCechPresheafResolution.diagram p X Y f hp n
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "FF" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor.IntrinsicPadicFrameFunctor.functor p X Y f hp n
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.baseDiagram (p := p)
  (J := Ideal.span {(p : W)}) (δ := γ) (f := w) (n := n)

local instance separated : IsSeparated w := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

abbrev localPairing := BoundedFrame.DiagramCechProduct.localPairing w n FF
abbrev site_natural := BoundedFrame.DiagramCechProduct.site_natural w n FF
abbrev frame_natural := BoundedFrame.DiagramCechProduct.frame_natural w n FF
abbrev pairing := BoundedFrame.DiagramCechProduct.pairing w n FF U
abbrev pairing_natural := BoundedFrame.DiagramCechProduct.pairing_natural w n FF U
abbrev local_differential := BoundedFrame.DiagramCechProduct.local_differential w n FF
abbrev pairing_differential := BoundedFrame.DiagramCechProduct.pairing_differential w n FF U

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.CechProduct.Intrinsic
