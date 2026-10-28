import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.Product
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.CoefficientPairing
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.BilinearPairing
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.SheafTensor

/-! # Sheaf Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafProduct

noncomputable section

/-! The native bounded relative PD sheaf complex carries the product
obtained from its original form presheaf. The literal sheafification unit
preserves that product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram F
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.baseDiagram (p := p) (J := J) (δ := δ) (f := f) (n := n)
local notation "π" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.projection F
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.complex F
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.coefficientPresheaves (p := p) (J := J) (δ := δ) f n
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex f n F

local instance monoidalSheafification :
    ((BoundedCrystalline.Site.topology (p := p) (J := J) (δ := δ) f n).W (A := ModuleCat.{u + 1} R)).IsMonoidal :=
  Module.SheafTensor.monoidal (BoundedCrystalline.Site.topology f n) R

def coefficientComplex := ((L).mapHomologicalComplex (.up ℕ)).obj P

def coefficientPairing (a b : ℕ)
    (U : (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ) :
    ((coefficientComplex f n F).X a).obj U →ₗ[R]
      ((coefficientComplex f n F).X b).obj U →ₗ[R]
        ((coefficientComplex f n F).X (a + b)).obj U :=
  Crystalline.CoefficientPairing.lift B _ _ _
    (RelativeCrystalline.Product.sectionPairing H Q π a b U)

theorem coefficientPairing_natural (a b : ℕ)
    {U V : (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ} (α : U ⟶ V)
    (x : ((coefficientComplex f n F).X a).obj U)
    (y : ((coefficientComplex f n F).X b).obj U) :
    ((coefficientComplex f n F).X (a + b)).map α (coefficientPairing f n F a b U x y) =
      coefficientPairing f n F a b V
        (((coefficientComplex f n F).X a).map α x)
        (((coefficientComplex f n F).X b).map α y) :=
  Crystalline.CoefficientPairing.map_lift B _ _ _
    ((P).X a |>.map α) ((P).X b |>.map α) ((P).X (a + b) |>.map α)
    (RelativeCrystalline.Product.sectionPairing H Q π a b U)
    (RelativeCrystalline.Product.sectionPairing H Q π a b V)
    (RelativeCrystalline.Product.sectionPairing_natural H Q π a b α) x y

def sectionPairing (a b : ℕ)
    (U : (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ) :
    ((K).X a).obj.obj U →ₗ[R] ((K).X b).obj.obj U →ₗ[R] ((K).X (a + b)).obj.obj U :=
  Sheafified.BilinearPairing.pairing R
    ((coefficientComplex f n F).X a) ((coefficientComplex f n F).X b)
    ((coefficientComplex f n F).X (a + b))
    (coefficientPairing f n F a b) (coefficientPairing_natural f n F a b) (BoundedCrystalline.Site.topology f n) U

theorem sectionPairing_natural (a b : ℕ)
    {U V : (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ} (α : U ⟶ V)
    (x : ((K).X a).obj.obj U) (y : ((K).X b).obj.obj U) :
    ((K).X (a + b)).obj.map α (sectionPairing f n F a b U x y) =
      sectionPairing f n F a b V (((K).X a).obj.map α x) (((K).X b).obj.map α y) :=
  Sheafified.BilinearPairing.pairing_natural R
    ((coefficientComplex f n F).X a) ((coefficientComplex f n F).X b)
    ((coefficientComplex f n F).X (a + b))
    (coefficientPairing f n F a b) (coefficientPairing_natural f n F a b) (BoundedCrystalline.Site.topology f n) α x y

def unitMap (a : ℕ) : (coefficientComplex f n F).X a ⟶ ((K).X a).obj :=
  (sheafificationAdjunction (BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} R)).unit.app
    ((coefficientComplex f n F).X a)

theorem unitMap_pairing (a b : ℕ)
    (U : (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ)
    (x : ((coefficientComplex f n F).X a).obj U)
    (y : ((coefficientComplex f n F).X b).obj U) :
    (unitMap f n F (a + b)).app U (coefficientPairing f n F a b U x y) =
      sectionPairing f n F a b U ((unitMap f n F a).app U x) ((unitMap f n F b).app U y) :=
  Sheafified.BilinearPairing.unit_pairing R
    ((coefficientComplex f n F).X a) ((coefficientComplex f n F).X b)
    ((coefficientComplex f n F).X (a + b))
    (coefficientPairing f n F a b) (coefficientPairing_natural f n F a b) (BoundedCrystalline.Site.topology f n) U x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafProduct
