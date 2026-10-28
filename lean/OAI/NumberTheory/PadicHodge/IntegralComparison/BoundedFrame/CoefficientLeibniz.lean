import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafProduct

/-! # Coefficient Leibniz -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.CoefficientLeibniz

noncomputable section

/-! The original PD Leibniz identity after the exact coefficient functor
used by the bounded relative sheaf resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafProduct

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram F
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.baseDiagram (p := p) (J := J) (δ := δ) (f := f) (n := n)
local notation "π" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.projection F
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.complex F
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafProduct.coefficientComplex f n F

theorem degreeCast_down {a b : ℕ} (h : a = b)
    (U : (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ) (x : ((L).X a).obj U) :
    (Presheaf.CechProduct.sectionDegreeCast L h U x).down =
      Presheaf.CechProduct.sectionDegreeCast P h U x.down := by
  subst b
  rfl

theorem differential (a b : ℕ)
    (U : (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ)
    (x : ((L).X a).obj U) (y : ((L).X b).obj U) :
    ((L).d (a + b) (a + b + 1)).app U (SheafProduct.coefficientPairing f n F a b U x y) =
      Presheaf.CechProduct.sectionDegreeCast L (by omega : (a + 1) + b = a + b + 1) U
        (SheafProduct.coefficientPairing f n F (a + 1) b U (((L).d a (a + 1)).app U x) y) +
      (-1 : ℤ) ^ a • Presheaf.CechProduct.sectionDegreeCast L
        (by omega : a + (b + 1) = a + b + 1) U
        (SheafProduct.coefficientPairing f n F a (b + 1) U x (((L).d b (b + 1)).app U y)) := by
  apply ULift.ext
  change ((P).d (a + b) (a + b + 1)).app U
      (RelativeCrystalline.Product.sectionPairing H Q π a b U x.down y.down) =
    (Presheaf.CechProduct.sectionDegreeCast L (by omega : (a + 1) + b = a + b + 1) U
      (SheafProduct.coefficientPairing f n F (a + 1) b U (((L).d a (a + 1)).app U x) y)).down +
    (-1 : ℤ) ^ a • (Presheaf.CechProduct.sectionDegreeCast L
      (by omega : a + (b + 1) = a + b + 1) U
      (SheafProduct.coefficientPairing f n F a (b + 1) U x (((L).d b (b + 1)).app U y))).down
  rw [degreeCast_down, degreeCast_down]
  exact RelativeCrystalline.Product.sectionPairing_differential H Q π a b U x.down y.down

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.CoefficientLeibniz
