import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.CechCoordinateUnit
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.CechCoefficientChange
import OAI.AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotient

/-! # Quotient Total -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.QuotientTotal.IntegralCechQuotientTotal

noncomputable section

/-! Quotienting the actual finite integral Cech total complex by a coefficient
ideal agrees with forming the Cech total of the quotient presheaf complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite Simplicial

variable (R : Type) [CommRing R] (X : Over (Spec (CommRingCat.of R)))
  {ι : Type} [Finite ι] (U : ι → X.left.Opens) (I : Ideal R)

local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex.FirstThreeComplex.complex (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.presheafComplex R X)
local notation "B" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.CechCoordinateUnit.IntegralAffineCechCoordinateUnit.bicomplex R X U
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Module.IdealQuotient.functor R I

def presheaves : (X.left.Opensᵒᵖ ⥤ ModuleCat.{0} R) ⥤ (X.left.Opensᵒᵖ ⥤ ModuleCat.{0} R) :=
  (Functor.whiskeringRight _ _ _).obj G

instance presheaves_additive : (presheaves R X I).Additive := by
  dsimp only [presheaves]
  infer_instance

local instance : (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor R X U).Additive := by
  change (FormalCoproduct.cochainComplexFunctor (FormalCoproduct.mk ι U).cech).Additive
  infer_instance

theorem finiteIndices (n : SimplexCategory) : Finite ((FormalCoproduct.mk ι U).cech.obj (op n)).I := by
  change Finite (Fin (n.len + 1) → ι)
  infer_instance

def bicomplex : HomologicalComplex₂ (ModuleCat.{0} R) (.up ℕ) (.up ℕ) :=
  ((AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.cechFunctor R X U).mapHomologicalComplex (.up ℕ)).obj
    (((presheaves R X I).mapHomologicalComplex (.up ℕ)).obj P)

def bicomplexIso : AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex G B ≅ bicomplex R X U I :=
  (NatIso.mapHomologicalComplex
    (GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.iso G (FormalCoproduct.mk ι U).cech (finiteIndices R X U))
      (.up ℕ)).app P

def iso : IntegralComparison.Module.IdealQuotient.complex R I ((B).total (.up ℕ)) ≅
    (bicomplex R X U I).total (.up ℕ) :=
  (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso G B).symm ≪≫
    HomologicalComplex₂.total.mapIso (bicomplexIso R X U I) (.up ℕ)

def homologyIso (i : ℕ) :
    (IntegralComparison.Module.IdealQuotient.complex R I ((B).total (.up ℕ))).homology i ≅
      ((bicomplex R X U I).total (.up ℕ)).homology i :=
  (HomologicalComplex.homologyFunctor _ _ i).mapIso (iso R X U I)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralCech.QuotientTotal.IntegralCechQuotientTotal
