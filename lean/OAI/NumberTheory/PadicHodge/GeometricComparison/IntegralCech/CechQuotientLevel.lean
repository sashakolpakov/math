import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.CechQuotientTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.QuotientLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.MappedTotalNaturality

/-! # Cech Quotient Level -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.CechQuotientLevel.IntegralCechQuotientLevel

noncomputable section

/-! Retaining the first three de Rham form degrees is compatible with
the actual coefficient-ideal transitions of integral Cech totals. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  {ι : Type} (U : ι → X.left.Opens) (I J : Ideal R) (hIJ : I ≤ J)

def rows : CechQuotientTotal.IntegralCechQuotientTotal.rows R X U I ⟶ CechQuotientTotal.IntegralCechQuotientTotal.rows R X U J :=
  Functor.whiskerRight (QuotientLevel.IntegralCechQuotientLevel.presheaves R X I J hIJ) (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor R X U)

def bicomplexMap : CechQuotientTotal.IntegralCechQuotientTotal.bicomplex R X U I ⟶ CechQuotientTotal.IntegralCechQuotientTotal.bicomplex R X U J :=
  ((rows R X U I J hIJ).mapHomologicalComplex (.up ℕ)).app (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)

def map : (CechQuotientTotal.IntegralCechQuotientTotal.bicomplex R X U I).total (.up ℕ) ⟶
    (CechQuotientTotal.IntegralCechQuotientTotal.bicomplex R X U J).total (.up ℕ) :=
  HomologicalComplex₂.total.map (bicomplexMap R X U I J hIJ) (.up ℕ)

theorem projection : CechQuotientTotal.IntegralCechQuotientTotal.projection R X U I ≫ QuotientLevel.IntegralCechQuotientLevel.map R X U I J hIJ =
    IntegralCechQuotientLevel.map R X U I J hIJ ≫ CechQuotientTotal.IntegralCechQuotientTotal.projection R X U J :=
  FirstThree.MappedTotalNaturality.FirstThreeMappedTotalNaturality.natural R (CechQuotientTotal.IntegralCechQuotientTotal.rows R X U I)
    (CechQuotientTotal.IntegralCechQuotientTotal.rows R X U J) (rows R X U I J hIJ) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)

theorem homology : HomologicalComplex.homologyMap (IntegralCechQuotientLevel.map R X U I J hIJ) 1 ≫
    (CechQuotientTotal.IntegralCechQuotientTotal.homologyIso R X U J).hom =
    (CechQuotientTotal.IntegralCechQuotientTotal.homologyIso R X U I).hom ≫
      HomologicalComplex.homologyMap (QuotientLevel.IntegralCechQuotientLevel.map R X U I J hIJ) 1 :=
  (HomologicalComplex.homologyMap_comp (IntegralCechQuotientLevel.map R X U I J hIJ) (CechQuotientTotal.IntegralCechQuotientTotal.projection R X U J) 1).symm.trans
    ((congrArg (fun q => HomologicalComplex.homologyMap q 1) (projection R X U I J hIJ).symm).trans
      (HomologicalComplex.homologyMap_comp (CechQuotientTotal.IntegralCechQuotientTotal.projection R X U I)
        (QuotientLevel.IntegralCechQuotientLevel.map R X U I J hIJ) 1))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.CechQuotientLevel.IntegralCechQuotientLevel
