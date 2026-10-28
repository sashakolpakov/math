import OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.FiniteAffineCechAcyclic
import OAI.AlgebraicGeometry.Crystalline.Cohomology.MixedCech.ComplexResolution
import OAI.NumberTheory.PadicHodge.GeometricComparison.TruncatedExt
import OAI.NumberTheory.PadicHodge.GeometricComparison.TotalExt

/-! # Cech Total Acyclic -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.CechTotalAcyclic.FlatBaseCechTotalAcyclic

noncomputable section

/-! # Acyclicity of the terms of the actual ordinary-form Čech total -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian Limits _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] [Module.Flat ℤ R]
  (X : Over (Spec (CommRingCat.of R))) [IsProper X.hom] [Smooth X.hom]
  {ι : Type u} [Finite ι] (U : ι → X.left.Opens) (hU : ∀ i, IsAffineOpen (U i))

local instance coefficientExt : HasExt.{u + 1} (DeRhamGlobalId.DeRhamGlobal.Sheaves R X) := HasExt.standard _
local instance : HasCoproducts.{0} (DeRhamGlobalId.DeRhamGlobal.Sheaves R X) := ZariskiColimitsCore.ZariskiColimits.coproducts R X.left

include hU in
theorem total (n q : ℕ) :
    Subsingleton (Ext.{u + 1} (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
      ((MixedCech.ComplexResolution.MixedCechComplexResolution.total R X.left U (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)).X n)
      (q + 1)) :=
  NumberTheory.PadicHodge.GeometricComparison.TotalExt.TotalExtVanishing.subsingleton (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
    (NumberTheory.PadicHodge.GeometricComparison.Functor.ResolutionBicomplex.FunctorResolutionBicomplex.bicomplex (MixedCech.Functor.MixedCechFunctor.sheafFunctor R X.left U)
      (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)) n (q + 1)
    (fun j p => FiniteAffineCechAcyclic.FlatBaseFiniteAffineCechAcyclic.term R X U hU j p q)

include hU in
theorem integerTotal (n : ℤ) (q : ℕ) :
    Subsingleton (Ext.{u + 1} (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
      ((MixedCech.ComplexResolution.MixedCechComplexResolution.integerTotal R X.left U (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)).X n)
      (q + 1)) :=
  NumberTheory.PadicHodge.GeometricComparison.TruncatedExt.TruncatedExtVanishing.extend (DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
    (MixedCech.ComplexResolution.MixedCechComplexResolution.total R X.left U (DeRhamGlobalId.DeRhamGlobal.sheafComplex R X))
    (total R X U hU) n q

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.FlatBase.CechTotalAcyclic.FlatBaseCechTotalAcyclic
