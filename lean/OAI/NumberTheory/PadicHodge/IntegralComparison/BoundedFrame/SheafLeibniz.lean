import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.CoefficientLeibniz
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.CochainPairing

/-! # Sheaf Leibniz -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafLeibniz.Product

noncomputable section

/-! The actual bounded relative PD sheaf complex, with its native
coefficient modules, satisfies the graded product differential rule. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex f n F

local instance monoidalSheafificationLeibniz :
    ((BoundedCrystalline.Site.topology (p := p) (J := J) (δ := δ) f n).W (A := ModuleCat.{u + 1} R)).IsMonoidal :=
  Module.SheafTensor.monoidal (BoundedCrystalline.Site.topology f n) R

def underlyingComplex :=
  ((sheafToPresheaf (BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} R)).mapHomologicalComplex (.up ℕ)).obj K

theorem sectionPairing_differential (a b : ℕ)
    (U : (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ)
    (x : ((underlyingComplex f n F).X a).obj U)
    (y : ((underlyingComplex f n F).X b).obj U) :
    ((underlyingComplex f n F).d (a + b) (a + b + 1)).app U (SheafProduct.sectionPairing f n F a b U x y) =
      Presheaf.CechProduct.sectionDegreeCast (underlyingComplex f n F)
        (by omega : (a + 1) + b = a + b + 1) U
        (SheafProduct.sectionPairing f n F (a + 1) b U
          (((underlyingComplex f n F).d a (a + 1)).app U x) y) +
      (-1 : ℤ) ^ a • Presheaf.CechProduct.sectionDegreeCast (underlyingComplex f n F)
        (by omega : a + (b + 1) = a + b + 1) U
        (SheafProduct.sectionPairing f n F a (b + 1) U x
          (((underlyingComplex f n F).d b (b + 1)).app U y)) :=
  Sheafified.CochainPairing.differential (BoundedCrystalline.Site.topology f n) R (SheafProduct.coefficientComplex f n F)
    (SheafProduct.coefficientPairing f n F) (SheafProduct.coefficientPairing_natural f n F)
    (CoefficientLeibniz.differential f n F) a b U x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafLeibniz.Product
