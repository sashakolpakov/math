import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.DeRhamLattice
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.FilteredOneBaseChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.SaturatedBase

/-! # Filtered Lattice -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The original integral Hodge lattice is exactly the inverse image of the original rational Hodge step. -/

open scoped TensorProduct

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem Geometry.AbelianH1Model.integral_generic_deRham_hone_filtration (r : ℤ) :
    ((AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℤ_[q] A.integral.scheme 1 r).baseChange ℚ_[q]).map
      A.integral_generic_deRham_hone.toLinearMap = A.Fil r :=
  Integral.FilteredOneBaseChange.IntegralGlobalHOneBaseChange.quasiCompactEquiv_filtration ℤ_[q] A.integral.scheme ℚ_[q]
    A.localFiber.scheme A.integralGenericMorphism A.integralGenericSquare r

theorem Geometry.AbelianH1Model.integralDeRhamInclusion_mem_hodge_iff
    (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1) :
    A.integralDeRhamInclusion x ∈ A.Fil 1 ↔
      x ∈ AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℤ_[q] A.integral.scheme 1 1 := by
  let := A.integral_hodge_quotient_free
  exact SaturatedBase.SaturatedBaseChange.equiv_mem_iff
    (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.filtration ℤ_[q] A.integral.scheme 1 1)
    A.integral_generic_deRham_hone (A.Fil 1) (A.integral_generic_deRham_hone_filtration 1) x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
