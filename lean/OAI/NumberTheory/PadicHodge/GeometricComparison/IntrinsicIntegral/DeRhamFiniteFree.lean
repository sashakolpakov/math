import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.IntrinsicFormCohomology
import OAI.NumberTheory.PadicHodge.GeometricComparison.LowDegree
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.Saturation
import Mathlib.LinearAlgebra.FreeModule.PID

/-! # De Rham Finite Free -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.DeRhamFiniteFree.AbelianModel

noncomputable section

/-! Native integral de Rham H-one and its first Hodge quotient are finite free modules. -/

open _root_.CategoryTheory

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

local instance : HasExt.{1} (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves ℤ_[q] A.integral.scheme) := HasExt.standard _

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.integral_deRham_hone_finite :
    Module.Finite ℤ_[q] (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1) := by
  let := Integral.IntrinsicFormCohomology.IntegralIntrinsicFormCohomology.sections_finite ℤ_[q] A.integral.scheme 1 (by omega)
  let : Module.Finite ℤ_[q] (Abelian.Ext.{1}
      (ConstantSheaf.ConstantSheafSections.coefficient ℤ_[q] (TopCat.of A.integral.scheme.left))
      ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex ℤ_[q] A.integral.scheme).X 0) 1) :=
    Integral.IntrinsicFormCohomology.IntegralIntrinsicFormCohomology.finite ℤ_[q] A.integral.scheme 0 (by omega) 1
  exact LowDegree.LowDegreeHypercohomologyFinite.finite ℤ_[q] A.integral.scheme.left
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex ℤ_[q] A.integral.scheme)

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.integral_deRham_hone_free :
    Module.Free ℤ_[q] (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1) := by
  let := A.integral_deRham_hone_finite
  let := A.integral_deRham_hone_torsionFree
  infer_instance

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.integral_hodge_finite :
    Module.Finite ℤ_[q] (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℤ_[q] A.integral.scheme 1 1) := by
  let := A.integral_deRham_hone_finite
  infer_instance

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.integral_hodge_free :
    Module.Free ℤ_[q] (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℤ_[q] A.integral.scheme 1 1) := by
  let := A.integral_deRham_hone_finite
  let := A.integral_deRham_hone_free
  infer_instance

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.integral_hodge_quotient_finite :
    Module.Finite ℤ_[q] (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1 ⧸
      AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℤ_[q] A.integral.scheme 1 1) := by
  let := A.integral_deRham_hone_finite
  infer_instance

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.integral_hodge_quotient_free :
    Module.Free ℤ_[q] (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1 ⧸
      AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℤ_[q] A.integral.scheme 1 1) := by
  let := A.integral_hodge_quotient_finite
  let := A.integral_hodge_quotient_torsionFree
  infer_instance

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.DeRhamFiniteFree.AbelianModel
