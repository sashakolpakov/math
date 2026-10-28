import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.CoherentCohomology
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeFormCoherence
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExtRight
import OAI.AlgebraicGeometry.SheafCohomology.AffineVanishing

/-! # Form Ext Vanishing -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.FormExtVanishing.IntegralAffineFormExtVanishing

noncomputable section

/-! Positive coefficient cohomology of the actual first three form sheaves vanishes on affine schemes over a flat integer algebra. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [Module.Flat ℤ R]
  (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]

local instance : HasExt.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) := HasExt.standard _

theorem module_ext_subsingleton (M : X.left.Modules) [M.IsQuasicoherent] (k : ℕ) :
    Subsingleton (Abelian.Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
      (IntegralComparison.AlgebraSheafScalars.obj R X M) (k + 1)) := by
  let : Subsingleton (AlgebraicGeometry.SheafCohomology.AffineH.Projective.H M (k + 1)) := AlgebraicGeometry.SheafCohomology.AffineVanishing.Projective.moduleAffineHSucc_subsingleton M k
  exact (Integral.CoherentCohomology.IntegralCoherentCohomology.additiveEquiv R X M (k + 1)).injective.subsingleton

theorem ext_subsingleton (n : ℕ) (hn : n ≤ 2) (k : ℕ) :
    Subsingleton (Abelian.Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
      ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X n) (k + 1)) := by
  let M := Integral.FormsModules.IntegralFormsModules.sheaf R X n
  let : M.IsQuasicoherent := IntegralFirst.ThreeFormCoherence.IntegralFirstThreeFormCoherence.quasicoherent R X n hn
  let : Subsingleton (Abelian.Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
      ((IntegralComparison.AlgebraSheafScalars.functor R X).obj (Integral.FormsModules.IntegralFormsModules.sheaf R X n)) (k + 1)) :=
    module_ext_subsingleton R X M k
  exact (ExtRight.ExtRightIsoLinear.equiv R (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
    (Integral.FormsModules.IntegralFormsModules.coefficientSheafIso R X n) (k + 1)).symm.injective.subsingleton

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralAffine.FormExtVanishing.IntegralAffineFormExtVanishing
