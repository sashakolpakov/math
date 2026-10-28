import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.QuotientTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechPresheaf.CoefficientTransformation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotientTransition

/-! # Quotient Level -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.QuotientLevel.IntegralCechQuotientLevel

noncomputable section

/-! The original quotient-of-total and total-of-quotient comparison
respects transitions of coefficient ideals on the integral Cech complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  {ι : Type} [Finite ι] (U : ι → X.left.Opens) (I J : Ideal R) (hIJ : I ≤ J)

local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex.FirstThreeComplex.complex (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)
local notation "B" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex R X U
local notation "FI" => OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotient.functor R I
local notation "FJ" => OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotient.functor R J
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotientTransition.transformation R I J hIJ

def presheaves : QuotientTotal.IntegralCechQuotientTotal.presheaves R X I ⟶ QuotientTotal.IntegralCechQuotientTotal.presheaves R X J :=
  CechPresheaf.CoefficientTransformation.CechPresheafCoefficientTransformation.presheaves FI FJ a

def complexMap : ((QuotientTotal.IntegralCechQuotientTotal.presheaves R X I).mapHomologicalComplex (.up ℕ)).obj P ⟶
    ((QuotientTotal.IntegralCechQuotientTotal.presheaves R X J).mapHomologicalComplex (.up ℕ)).obj P :=
  ((presheaves R X I J hIJ).mapHomologicalComplex (.up ℕ)).app P

def bicomplexMap : QuotientTotal.IntegralCechQuotientTotal.bicomplex R X U I ⟶ QuotientTotal.IntegralCechQuotientTotal.bicomplex R X U J :=
  ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor R X U).mapHomologicalComplex (.up ℕ)).map (complexMap R X I J hIJ)

def map : (QuotientTotal.IntegralCechQuotientTotal.bicomplex R X U I).total (.up ℕ) ⟶
    (QuotientTotal.IntegralCechQuotientTotal.bicomplex R X U J).total (.up ℕ) :=
  HomologicalComplex₂.total.map (bicomplexMap R X U I J hIJ) (.up ℕ)

theorem natural : IntegralComparison.Module.IdealQuotientTransition.complexMap R I J hIJ ((B).total (.up ℕ)) ≫
    (QuotientTotal.IntegralCechQuotientTotal.iso R X U J).hom =
      (QuotientTotal.IntegralCechQuotientTotal.iso R X U I).hom ≫ IntegralCechQuotientLevel.map R X U I J hIJ :=
  CechPresheaf.CoefficientTransformation.CechPresheafCoefficientTransformation.total FI FJ a (FormalCoproduct.mk ι U).cech
    (QuotientTotal.IntegralCechQuotientTotal.finiteIndices R X U) P

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.QuotientLevel.IntegralCechQuotientLevel
