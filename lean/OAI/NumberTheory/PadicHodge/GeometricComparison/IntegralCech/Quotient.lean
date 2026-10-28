import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.CechQuotientTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.MappedTotal
import OAI.NumberTheory.PadicHodge.IntegralComparison.InverseCoordinateHomology

/-! # Quotient -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.Quotient.IntegralCechQuotientHodge

noncomputable section

/-! The inverse of the original full-to-three-form quotient comparison
carries each first-three-form Hodge representative to a full-form representative. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  {ι : Type} (U : ι → X.left.Opens) (I : Ideal R) (r : ℤ)

local notation "B" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal.bicomplex R X U I
local notation "L" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.QuotientTotal.IntegralCechQuotientTotal.bicomplex R X U I

def truncatedIso : (HomologicalComplex₂.total (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal B r) (.up ℕ)).homology 1 ≅
    (HomologicalComplex₂.total (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal L r) (.up ℕ)).homology 1 :=
  FirstThree.MappedTotal.FirstThreeMappedTotalHodge.homologyIso R (CechQuotientTotal.IntegralCechQuotientTotal.rows R X U I)
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X) r

theorem inclusion :
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion B r) (.up ℕ)) 1 ≫
      (CechQuotientTotal.IntegralCechQuotientTotal.homologyIso R X U I).hom =
    (truncatedIso R X U I r).hom ≫
      HomologicalComplex.homologyMap (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r) (.up ℕ)) 1 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom (FirstThree.MappedTotal.FirstThreeMappedTotalHodge.inclusion R
    (CechQuotientTotal.IntegralCechQuotientTotal.rows R X U I) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X) r) x

theorem inverse_inclusion :
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r) (.up ℕ)) 1 ≫
      (CechQuotientTotal.IntegralCechQuotientTotal.homologyIso R X U I).inv =
    (truncatedIso R X U I r).inv ≫
      HomologicalComplex.homologyMap (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion B r) (.up ℕ)) 1 :=
  IntegralComparison.InverseCoordinateHomology.inverse (truncatedIso R X U I r)
    (CechQuotientTotal.IntegralCechQuotientTotal.homologyIso R X U I)
    (HomologicalComplex.homologyMap (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion B r) (.up ℕ)) 1)
    (HomologicalComplex.homologyMap (HomologicalComplex₂.total.map (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion L r) (.up ℕ)) 1)
    (inclusion R X U I r)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.Quotient.IntegralCechQuotientHodge
