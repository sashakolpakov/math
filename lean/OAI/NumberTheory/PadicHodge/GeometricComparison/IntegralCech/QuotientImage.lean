import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.QuotientTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.QuotientTotalImage

/-! # Quotient Image -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.QuotientImage.IntegralCechQuotientHodgeImage

noncomputable section

/-! The actual quotient-of-total comparison carries reduced native
integral Hodge representatives into the quotient Cech Hodge image. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  {ι : Type} [Finite ι] (U : ι → X.left.Opens) (I : Ideal R)

local notation "B" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex R X U
local notation "L" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.QuotientTotal.IntegralCechQuotientTotal.bicomplex R X U I

def truncatedMap (r : ℤ) : HomologicalComplex₂.total (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal B r) (.up ℕ) ⟶
    HomologicalComplex₂.total (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal L r) (.up ℕ) :=
  QuotientTotalImage.QuotientTotalHodgeImage.truncatedMap R I (QuotientTotal.IntegralCechQuotientTotal.bicomplexIso R X U I) r

theorem inclusion (r : ℤ) :
    HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion B r) (.up ℕ) ≫
      IntegralComparison.Module.IdealQuotient.complexProjection R I ((B).total (.up ℕ)) ≫
        (QuotientTotal.IntegralCechQuotientTotal.iso R X U I).hom =
    truncatedMap R X U I r ≫ HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r) (.up ℕ) :=
  QuotientTotalImage.QuotientTotalHodgeImage.inclusion R I (QuotientTotal.IntegralCechQuotientTotal.bicomplexIso R X U I) r

theorem homology_inclusion (n : ℕ) (r : ℤ) :
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion B r) (.up ℕ)) n ≫
      HomologicalComplex.homologyMap (IntegralComparison.Module.IdealQuotient.complexProjection R I ((B).total (.up ℕ))) n ≫
        (QuotientTotal.IntegralCechQuotientTotal.homologyIso R X U I n).hom =
    HomologicalComplex.homologyMap (truncatedMap R X U I r) n ≫
      HomologicalComplex.homologyMap (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r) (.up ℕ)) n := by
  have h := QuotientTotalImage.QuotientTotalHodgeImage.homology_inclusion R I
    (QuotientTotal.IntegralCechQuotientTotal.bicomplexIso R X U I) n r
  have hm := HomologicalComplex.homologyMap_comp
    (IntegralComparison.Module.IdealQuotient.complexProjection R I ((B).total (.up ℕ)))
    (QuotientTotal.IntegralCechQuotientTotal.iso R X U I).hom n
  exact (congrArg (fun a => HomologicalComplex.homologyMap
    (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion B r) (.up ℕ)) n ≫ a) hm).symm.trans h

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.QuotientImage.IntegralCechQuotientHodgeImage
