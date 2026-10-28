import OAI.NumberTheory.PadicHodge.GeometricComparison.First.ZeroSaturatedImage
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.FunctionsOne

/-! # Saturation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The first native integral Hodge step has torsion-free quotient in actual de Rham H-one. -/

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem Geometry.AbelianH1Model.integral_hodge_quotient_torsionFree :
    Module.IsTorsionFree ℤ_[q]
      (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1 ⧸
        AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℤ_[q] A.integral.scheme 1 1) := by
  let := A.integral_functions_hone_torsionFree
  exact First.ZeroSaturatedImage.FirstZeroComplex.hodge_quotient_torsionFree ℤ_[q]
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex ℤ_[q] A.integral.scheme)
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf ℤ_[q] A.integral.scheme)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
