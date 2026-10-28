import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.CoherentCohomology
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FormCoherence
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExtRight

/-! # Intrinsic Form Cohomology -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.IntrinsicFormCohomology.IntegralIntrinsicFormCohomology

noncomputable section

/-! Properness gives finite coefficient cohomology of the actual first two native form sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (R : Type) [CommRing R] [Module.Flat ℤ R] [IsNoetherianRing R]
  (X : Over (Spec (CommRingCat.of R))) [Smooth X.hom] [IsProper X.hom]

local instance : HasExt.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves R X) := HasExt.standard _

theorem finite (n : ℕ) (hn : n ≤ 1) (k : ℕ) :
    Module.Finite R (Abelian.Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
      ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X n) k) := by
  let M := FormsModules.IntegralFormsModules.sheaf R X n
  let : M.IsQuasicoherent := FormCoherence.IntegralFormCoherence.quasicoherent R X n hn
  let : M.IsFiniteType := FormCoherence.IntegralFormCoherence.finiteType R X n hn
  let : Module.Finite R (Abelian.Ext.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
      ((IntegralComparison.AlgebraSheafScalars.functor R X).obj (FormsModules.IntegralFormsModules.sheaf R X n)) k) :=
    CoherentCohomology.IntegralCoherentCohomology.finite R X M k
  exact Module.Finite.equiv (ExtRight.ExtRightIsoLinear.equiv R (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf R X)
    (FormsModules.IntegralFormsModules.coefficientSheafIso R X n) k)

theorem sections_finite (n : ℕ) (hn : n ≤ 1) :
    Module.Finite R (((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X n).obj.obj (op ⊤)) := by
  let : Module.Finite R (Abelian.Ext.{1} (ConstantSheaf.ConstantSheafSections.coefficient R (TopCat.of X.left))
      ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X n) 0) := finite R X n hn 0
  exact Module.Finite.equiv ((Abelian.Ext.linearEquiv₀ (R := R)).trans
    (ConstantSheaf.ConstantSheafSections.linearEquiv R X.left ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex R X).X n)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.IntrinsicFormCohomology.IntegralIntrinsicFormCohomology
