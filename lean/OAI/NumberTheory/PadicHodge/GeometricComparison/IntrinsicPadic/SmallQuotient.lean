import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FirstThreeCrystalline
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.QuotientImage
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.Quotient
import OAI.NumberTheory.PadicHodge.GeometricComparison.NaturalTotalIso

/-! # Small Quotient -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallQuotient.IntrinsicPadicSmallQuotientHodge

noncomputable section

/-! The original principal reduction and inverse source comparison
preserve the actual form-degree Hodge image on the native small Cech total. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (n : ℕ)

local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X
local notation "V" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve V
local notation "I" => (Ideal.span {(p : ℤ_[p])}) ^ (n + 1)
local notation "B" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex ℤ_[p] X U
local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.QuotientTotal.IntegralCechQuotientTotal.bicomplex ℤ_[p] X U I
local notation "L" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.bicomplex ℤ_[p] X U I

def bicomplex : HomologicalComplex₂ (ModuleCat.{0} ℤ_[p]) (.up ℕ) (.up ℕ) :=
  CechPresheaf.CoefficientTotal.CechPresheafCoefficientTotal.bicomplex E
    (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (Coefficient.IntrinsicPadicSmallQuotientTotal.diagram p X n))

def openTruncatedIso (r : ℤ) :
    (HomologicalComplex₂.total (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (bicomplex p X n) r) (.up ℕ)).homology 1 ≅
    (HomologicalComplex₂.total (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal L r) (.up ℕ)).homology 1 :=
  NaturalTotalIso.NaturalTotalHodgeIso.homologyIso.{0, 0} ℤ_[p]
    (NaturalTotalIso.NaturalTotalHodgeIso.truncatedIso.{0, 0} ℤ_[p]
      (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.bicomplexIso ℤ_[p] X V I) r) 1

theorem source_inverse : (FirstThreeCrystalline.IntrinsicPadicFirstThreeCrystalline.sourceHomologyIso p X n).inv =
    (IntegralCech.QuotientTotal.IntegralCechQuotientTotal.homologyIso ℤ_[p] X U I 1).hom ≫
      (IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.homologyIso ℤ_[p] X U I).inv ≫
        HomologicalComplex.homologyMap (Coefficient.IntrinsicPadicSmallQuotientTotal.fullOpenIso p X n).inv 1 := rfl

def truncatedMap (r : ℤ) :
    (HomologicalComplex₂.total (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal B r) (.up ℕ)).homology 1 ⟶
    (HomologicalComplex₂.total (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (bicomplex p X n) r) (.up ℕ)).homology 1 :=
  HomologicalComplex.homologyMap (IntegralCech.QuotientImage.IntegralCechQuotientHodgeImage.truncatedMap ℤ_[p] X U I r) 1 ≫
    (IntegralCech.Quotient.IntegralCechQuotientHodge.truncatedIso ℤ_[p] X U I r).inv ≫ (openTruncatedIso p X n r).inv

theorem inclusion (r : ℤ) :
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion B r) (.up ℕ)) 1 ≫
      HomologicalComplex.homologyMap (PrincipalCochainExact.PrincipalCochainQuotient.projection ℤ_[p]
        (IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion.complex ℤ_[p] X U) (p : ℤ_[p]) (n + 1)) 1 ≫
        (FirstThreeCrystalline.IntrinsicPadicFirstThreeCrystalline.sourceHomologyIso p X n).inv =
    truncatedMap p X n r ≫ HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (bicomplex p X n) r) (.up ℕ)) 1 := by
  let i := HomologicalComplex.homologyMap
    (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion B r) (.up ℕ)) 1
  let a := HomologicalComplex.homologyMap (PrincipalCochainExact.PrincipalCochainQuotient.projection ℤ_[p]
    (IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion.complex ℤ_[p] X U) (p : ℤ_[p]) (n + 1)) 1 ≫
      (IntegralCech.QuotientTotal.IntegralCechQuotientTotal.homologyIso ℤ_[p] X U I 1).hom
  let b := (IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.homologyIso ℤ_[p] X U I).inv
  let c := HomologicalComplex.homologyMap (Coefficient.IntrinsicPadicSmallQuotientTotal.fullOpenIso p X n).inv 1
  let d := HomologicalComplex.homologyMap (IntegralCech.QuotientImage.IntegralCechQuotientHodgeImage.truncatedMap ℤ_[p] X U I r) 1
  let e := (IntegralCech.Quotient.IntegralCechQuotientHodge.truncatedIso ℤ_[p] X U I r).inv
  let f := (openTruncatedIso p X n r).inv
  let j := HomologicalComplex.homologyMap
    (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion Q r) (.up ℕ)) 1
  let k := HomologicalComplex.homologyMap
    (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r) (.up ℕ)) 1
  let l := HomologicalComplex.homologyMap
    (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion (bicomplex p X n) r) (.up ℕ)) 1
  have h₁ : i ≫ a = d ≫ j := IntegralCech.QuotientImage.IntegralCechQuotientHodgeImage.homology_inclusion ℤ_[p] X U I 1 r
  have h₂ : j ≫ b = e ≫ k := IntegralCech.Quotient.IntegralCechQuotientHodge.inverse_inclusion ℤ_[p] X U I r
  have h₃ : k ≫ c = f ≫ l := NaturalTotalIso.NaturalTotalHodgeIso.inverse_inclusion.{0, 0} ℤ_[p]
    (OrdinaryAffineTotal.OrdinaryAffineQuotientCech.bicomplexIso ℤ_[p] X V I) 1 r
  have h := ExactHomology.ExactHomologyComparison.compose i a b d j e k h₁ h₂
  have h' := ExactHomology.ExactHomologyComparison.compose i (a ≫ b) c (d ≫ e) k f l h h₃
  rw [source_inverse]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom h' x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SmallQuotient.IntrinsicPadicSmallQuotientHodge
