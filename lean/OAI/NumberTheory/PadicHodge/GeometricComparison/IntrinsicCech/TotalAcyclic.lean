import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Resolution
import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.AffineCechAcyclic
import OAI.NumberTheory.PadicHodge.GeometricComparison.TruncatedExt
import OAI.NumberTheory.PadicHodge.GeometricComparison.TotalExt
import OAI.AlgebraicGeometry.Comparison.Betti.Finite.TotalDiagonal

/-! # Total Acyclic -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.TotalAcyclic.IntrinsicCechTotalAcyclic

noncomputable section

/-! The actual finite affine Čech–de Rham total complex has acyclic terms for native coefficient Ext. -/

open _root_.CategoryTheory Abelian Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [Algebra ℚ R]
  (X : Over (Spec (CommRingCat.of R))) [IsSeparated X.hom]
  {ι : Type} [Finite ι] (U : ι → X.left.Opens) (hU : ∀ i, IsAffineOpen (U i))

local instance : HasExt.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) := HasExt.standard _
local instance : HasCoproducts.{0} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) :=
  Instances.IntrinsicCechInstances.hasCoproducts R X.left
local instance : (Functor.IntrinsicCechFunctor.sheafFunctor R X.left U).Additive :=
  Instances.IntrinsicCechInstances.additive R X.left U

include hU in
theorem total_ext_subsingleton (n q : ℕ) :
    Subsingleton (Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
      ((Resolution.IntrinsicCechResolution.total R X.left U (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)).X n) (q + 1)) :=
  TotalExt.TotalExtVanishing.subsingleton (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
    (Bicomplex.IntrinsicCechBicomplex.bicomplex R X.left U (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)) n (q + 1)
    (fun j p => GeometricComparison.Finite.AffineCechAcyclic.FiniteAffineCechAcyclic.sheafComplex_ext_subsingleton R X U hU j p q)

include hU in
theorem integerTotal_ext_subsingleton (n : ℤ) (q : ℕ) :
    Subsingleton (Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
      ((Resolution.IntrinsicCechResolution.integerTotal R X.left U (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)).X n) (q + 1)) :=
  TruncatedExt.TruncatedExtVanishing.extend (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
    (Resolution.IntrinsicCechResolution.total R X.left U (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X))
    (total_ext_subsingleton R X U hU) n q

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.TotalAcyclic.IntrinsicCechTotalAcyclic
