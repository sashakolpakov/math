import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.QuotientTotal
import OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.MappedTotalOne

/-! # Cech Quotient Total -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal

noncomputable section

/-! The full ordinary de Rham coefficient-quotient Cech total has the same
H-one as the original integral three-term quotient total. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  {ι : Type} (U : ι → X.left.Opens) (I : Ideal R)

local instance cech_additive : (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor R X U).Additive := by
  change (FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk ι U).cech).Additive
  infer_instance

def rows := QuotientTotal.IntegralCechQuotientTotal.presheaves R X I ⋙ AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor R X U

instance rows_additive : (rows R X U I).Additive := by
  dsimp only [rows]
  infer_instance

def bicomplex : HomologicalComplex₂ (ModuleCat.{0} R) (.up ℕ) (.up ℕ) :=
  ((rows R X U I).mapHomologicalComplex (.up ℕ)).obj (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)

def projection : (bicomplex R X U I).total (.up ℕ) ⟶
    (QuotientTotal.IntegralCechQuotientTotal.bicomplex R X U I).total (.up ℕ) :=
  FirstThree.MappedTotalOne.FirstThreeMappedTotalHOne.map R (rows R X U I) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)

theorem quasiIsoAt : QuasiIsoAt (projection R X U I) 1 :=
  FirstThree.MappedTotalOne.FirstThreeMappedTotalHOne.quasiIsoAt R (rows R X U I) (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)

def homologyIso : ((bicomplex R X U I).total (.up ℕ)).homology 1 ≅
    ((QuotientTotal.IntegralCechQuotientTotal.bicomplex R X U I).total (.up ℕ)).homology 1 := by
  let := quasiIsoAt R X U I
  exact isoOfQuasiIsoAt (projection R X U I) 1

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.CechQuotientTotal.IntegralCechQuotientTotal
