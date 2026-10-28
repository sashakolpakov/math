import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FiniteAffineCechAcyclic
import OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.Terms
import OAI.NumberTheory.PadicHodge.GeometricComparison.TotalExt
import OAI.NumberTheory.PadicHodge.GeometricComparison.TruncatedExt

/-! # Three Cech Acyclic -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechAcyclic.IntegralFirstThreeCechAcyclic

noncomputable section

/-! The finite affine Čech total complexes of native integral forms through degree two have acyclic terms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.CategoryTheory.Limits ZeroObject _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] [Module.Flat ℤ R]
  (X : Over (Spec (CommRingCat.of R))) [IsSeparated X.hom]
  {ι : Type} [Finite ι] (U : ι → X.left.Opens) (hU : ∀ i, IsAffineOpen (U i))

local notation "V" => OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X
local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.FirstThree.ThreeComplex.FirstThreeComplex.complex (OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X)
local notation "A" => OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X

local instance : HasExt.{1} V := HasExt.standard _
local instance : HasCoproducts.{0} V := IntrinsicCech.Instances.IntrinsicCechInstances.hasCoproducts R X.left

include hU in
theorem term_ext_subsingleton (j p q : ℕ) :
    Subsingleton (Ext.{1} A (((IntrinsicCech.Functor.IntrinsicCechFunctor.sheafFunctor R X.left U).obj ((K).X j)).X p) (q + 1)) := by
  let G := IntrinsicCech.Functor.IntrinsicCechFunctor.sheafFunctor R X.left U ⋙ HomologicalComplex.eval V (.up ℕ) p
  let H := (extFunctor.{1} (q + 1) : Vᵒᵖ ⥤ V ⥤ AddCommGrpCat.{1}).obj (op A)
  have : H.Additive := inferInstanceAs (extFunctorObj A (q + 1)).Additive
  rcases j with _ | (_ | (_ | j))
  · exact Integral.FiniteAffineCechAcyclic.IntegralFiniteAffineCechAcyclic.sheafComplex_ext_subsingleton R X U hU 0 (by omega) p q
  · exact Integral.FiniteAffineCechAcyclic.IntegralFiniteAffineCechAcyclic.sheafComplex_ext_subsingleton R X U hU 1 (by omega) p q
  · exact Integral.FiniteAffineCechAcyclic.IntegralFiniteAffineCechAcyclic.sheafComplex_ext_subsingleton R X U hU 2 (by omega) p q
  · exact AddCommGrpCat.subsingleton_of_isZero (H.map_isZero (G.map_isZero (isZero_zero _)))

include hU in
theorem total_ext_subsingleton (n q : ℕ) :
    Subsingleton (Ext.{1} A ((IntrinsicCech.Resolution.IntrinsicCechResolution.total R X.left U K).X n) (q + 1)) :=
  TotalExt.TotalExtVanishing.subsingleton A (IntrinsicCech.Bicomplex.IntrinsicCechBicomplex.bicomplex R X.left U K) n (q + 1)
    (fun j p => term_ext_subsingleton R X U hU j p q)

include hU in
theorem integerTotal_ext_subsingleton (n : ℤ) (q : ℕ) :
    Subsingleton (Ext.{1} A ((IntrinsicCech.Resolution.IntrinsicCechResolution.integerTotal R X.left U K).X n) (q + 1)) :=
  TruncatedExt.TruncatedExtVanishing.extend A (IntrinsicCech.Resolution.IntrinsicCechResolution.total R X.left U K)
    (total_ext_subsingleton R X U hU) n q

include hU in
theorem truncated_term_ext_subsingleton (r : ℤ) (j p q : ℕ) :
    Subsingleton (Ext.{1} A (((IntrinsicCech.Functor.IntrinsicCechFunctor.sheafFunctor R X.left U).obj
      ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r).X j)).X p) (q + 1)) := by
  let G := IntrinsicCech.Functor.IntrinsicCechFunctor.sheafFunctor R X.left U ⋙ HomologicalComplex.eval V (.up ℕ) p
  let H := (extFunctor.{1} (q + 1) : Vᵒᵖ ⥤ V ⥤ AddCommGrpCat.{1}).obj (op A)
  have : H.Additive := inferInstanceAs (extFunctorObj A (q + 1)).Additive
  change Subsingleton (H.obj (G.obj (if r ≤ (j : ℤ) then (K).X j else 0)))
  split_ifs with hj
  · exact term_ext_subsingleton R X U hU j p q
  · exact AddCommGrpCat.subsingleton_of_isZero (H.map_isZero (G.map_isZero (isZero_zero _)))

include hU in
theorem truncated_total_ext_subsingleton (r : ℤ) (n q : ℕ) :
    Subsingleton (Ext.{1} A
      ((IntrinsicCech.Resolution.IntrinsicCechResolution.total R X.left U (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r)).X n) (q + 1)) :=
  TotalExt.TotalExtVanishing.subsingleton A
    (IntrinsicCech.Bicomplex.IntrinsicCechBicomplex.bicomplex R X.left U (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r)) n (q + 1)
    (fun j p => truncated_term_ext_subsingleton R X U hU r j p q)

include hU in
theorem truncated_integerTotal_ext_subsingleton (r n : ℤ) (q : ℕ) :
    Subsingleton (Ext.{1} A
      ((IntrinsicCech.Resolution.IntrinsicCechResolution.integerTotal R X.left U (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r)).X n) (q + 1)) :=
  TruncatedExt.TruncatedExtVanishing.extend A
    (IntrinsicCech.Resolution.IntrinsicCechResolution.total R X.left U (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K r))
    (truncated_total_ext_subsingleton R X U hU r) n q

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechAcyclic.IntegralFirstThreeCechAcyclic
