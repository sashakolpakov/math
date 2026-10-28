import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Resolution
import OAI.NumberTheory.PadicHodge.GeometricComparison.TruncatedCech
import OAI.NumberTheory.PadicHodge.GeometricComparison.TotalExt
import OAI.NumberTheory.PadicHodge.GeometricComparison.TruncatedExt

/-! # Truncated Total Acyclic -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.TruncatedTotalAcyclic.IntrinsicCechTruncatedTotalAcyclic

noncomputable section

/-! Every actual Hodge-truncated native Čech total complex has coefficient-Ext-acyclic terms. -/

open _root_.CategoryTheory Abelian Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [Algebra ℚ R]
  (X : Over (Spec (CommRingCat.of R))) [IsSeparated X.hom]
  {ι : Type} [Finite ι] (U : ι → X.left.Opens) (hU : ∀ i, IsAffineOpen (U i))

local instance : HasExt.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) := HasExt.standard _
local instance : HasCoproducts.{0} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) :=
  Instances.IntrinsicCechInstances.hasCoproducts R X.left

include hU in
theorem total_ext_subsingleton (r : ℤ) (n q : ℕ) :
    Subsingleton (Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
      ((Resolution.IntrinsicCechResolution.total R X.left U
        (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) r)).X n) (q + 1)) :=
  TotalExt.TotalExtVanishing.subsingleton (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
    (Bicomplex.IntrinsicCechBicomplex.bicomplex R X.left U
      (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) r)) n (q + 1)
    (fun j p => TruncatedCech.TruncatedCechAcyclic.term_ext_subsingleton R X U hU r j p q)

include hU in
theorem integerTotal_ext_subsingleton (r n : ℤ) (q : ℕ) :
    Subsingleton (Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
      ((Resolution.IntrinsicCechResolution.integerTotal R X.left U
        (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) r)).X n) (q + 1)) :=
  TruncatedExt.TruncatedExtVanishing.extend (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
    (Resolution.IntrinsicCechResolution.total R X.left U (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X) r))
    (total_ext_subsingleton R X U hU r) n q

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.TruncatedTotalAcyclic.IntrinsicCechTruncatedTotalAcyclic
