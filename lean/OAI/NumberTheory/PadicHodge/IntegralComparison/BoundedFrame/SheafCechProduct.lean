import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafLeibniz
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.CohomologyProduct

/-! # Sheaf Cech Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafCechProduct

noncomputable section

/-! Products on the actual bounded frame sheaf Čech total. The literal
coefficient-presheaf to sheaf-complex map preserves the product on cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafLeibniz.Product

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafProduct.coefficientComplex f n F
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafLeibniz.Product.underlyingComplex f n F

def sheafificationMap : L ⟶ K where
  f a := SheafProduct.unitMap f n F a
  comm' a b _ := ((sheafificationAdjunction (BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} R)).unit.naturality
    ((L).d a b)).symm

variable (N : SimplicialObject (FormalCoproduct.{u} (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)))

def coefficientTotal := Presheaf.TotalCup.CechProduct.total.{u + 1, u, u, u + 1, u + 1} N L
def total := Presheaf.TotalCup.CechProduct.total.{u + 1, u, u, u + 1, u + 1} N K

def coefficientCup (a b : ℕ) :=
  Presheaf.CohomologyProduct.Cech.cohomologyCup.{u + 1, u, u, u + 1, u + 1} N L (SheafProduct.coefficientPairing f n F)
    (SheafProduct.coefficientPairing_natural f n F) (CoefficientLeibniz.differential f n F) a b

def cup (a b : ℕ) :=
  Presheaf.CohomologyProduct.Cech.cohomologyCup.{u + 1, u, u, u + 1, u + 1} N K (SheafProduct.sectionPairing f n F)
    (SheafProduct.sectionPairing_natural f n F) (SheafLeibniz.Product.sectionPairing_differential f n F) a b

def totalMap : coefficientTotal f n F N ⟶ total f n F N :=
  Presheaf.CechProductNaturality.totalMap.{u + 1, u, u, u + 1, u + 1} N (sheafificationMap f n F)

theorem totalMap_cup (a b : ℕ)
    (x : (coefficientTotal f n F N).homology a) (y : (coefficientTotal f n F N).homology b) :
    HomologicalComplex.homologyMap (totalMap f n F N) (a + b)
      (coefficientCup f n F N a b x y) = cup f n F N a b
      (HomologicalComplex.homologyMap (totalMap f n F N) a x)
      (HomologicalComplex.homologyMap (totalMap f n F N) b y) :=
  Presheaf.CohomologyProduct.Cech.totalMap_cohomologyCup.{u + 1, u, u, u + 1, u + 1} N L (SheafProduct.coefficientPairing f n F)
    (SheafProduct.coefficientPairing_natural f n F) (CoefficientLeibniz.differential f n F)
    K (SheafProduct.sectionPairing f n F) (SheafProduct.sectionPairing_natural f n F) (SheafLeibniz.Product.sectionPairing_differential f n F)
    (sheafificationMap f n F) (SheafProduct.unitMap_pairing f n F) a b x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafCechProduct
