import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.CechProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SheafComplexProduct

/-! # Sheaf Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.SheafProduct.Intrinsic

noncomputable section

/-! The literal global p-adic-model crystalline sheaf resolution
inherits its native coefficient product and graded Leibniz rule. -/

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

local notation "CR" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "L" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechPresheafResolution.IntrinsicPadicCechPresheafResolution.total p X Y f hp n U
local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSheafResolution.IntrinsicPadicCechSheafResolution.complex p X Y f hp n
local notation "μ" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.CechProduct.Intrinsic.pairing p X Y f hp n
local notation "hμ" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.CechProduct.Intrinsic.pairing_natural p X Y f hp n
local notation "dμ" => OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.CechProduct.Intrinsic.pairing_differential p X Y f hp n

local instance monoidal : ((BoundedCrystalline.Site.topology (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n).W (A := ModuleCat.{1} CR)).IsMonoidal :=
  Module.SheafTensor.monoidal (BoundedCrystalline.Site.topology (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n) CR

def coefficientComplex := Crystalline.SheafComplexProduct.coefficientComplex W L

def underlyingComplex : CochainComplex (Dᵒᵖ ⥤ ModuleCat.{1} CR) ℕ :=
  ((sheafToPresheaf (BoundedCrystalline.Site.topology (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n) (ModuleCat.{1} CR)).mapHomologicalComplex (.up ℕ)).obj K

def sectionPairing (a b : ℕ) (T : Dᵒᵖ) :
    ((K).X a).obj.obj T →ₗ[CR] ((K).X b).obj.obj T →ₗ[CR] ((K).X (a + b)).obj.obj T :=
  Crystalline.SheafComplexProduct.sectionPairing W (BoundedCrystalline.Site.topology (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n) L μ hμ a b T

abbrev sectionPairing_natural := Crystalline.SheafComplexProduct.sectionPairing_natural
  W (BoundedCrystalline.Site.topology (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n) L μ hμ

abbrev sectionPairing_differential := Crystalline.SheafComplexProduct.sectionPairing_differential
  W (BoundedCrystalline.Site.topology (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n) L μ hμ dμ

abbrev unit_pairing := Crystalline.SheafComplexProduct.unit_pairing W (BoundedCrystalline.Site.topology (p := p) (J := Ideal.span {(p : W)}) (δ := γ) w n) L μ hμ

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.SheafProduct.Intrinsic
