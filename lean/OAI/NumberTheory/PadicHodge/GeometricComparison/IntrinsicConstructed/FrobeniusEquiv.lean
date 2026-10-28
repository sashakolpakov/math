import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicConstructed.IntegralFrobenius
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cohomology.Invertibility
import OAI.NumberTheory.PadicHodge.GeometricComparison.WeakAdmissibilityTransport

/-! # Frobenius Equiv -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The constructed integral operator intertwines the actual lattice
inclusion with the conjugate of the original invertible crystalline Frobenius. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem Geometry.AbelianH1Model.constructedDeRhamFrobenius_equiv (hCohomology : Cohomology.Good.GoodReductionInput.{0}) :
    A.constructedDeRhamFrobenius =
      (WeakAdmissibilityTransport.FiltrationTransport.conjugateEquiv A.constructedCrystallineDeRhamEquiv
        (A.crystallineFrobeniusEquiv hCohomology)).toLinearMap := by
  rw [WeakAdmissibilityTransport.FiltrationTransport.conjugateEquiv_toLinearMap, A.crystallineFrobeniusEquiv_toLinearMap]
  rfl

theorem Geometry.AbelianH1Model.constructedIntegralFrobenius_inclusion_equiv (hCohomology : Cohomology.Good.GoodReductionInput.{0})
    (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1) :
    A.integralDeRhamInclusion (A.constructedIntegralFrobenius x) =
      WeakAdmissibilityTransport.FiltrationTransport.conjugateEquiv A.constructedCrystallineDeRhamEquiv
        (A.crystallineFrobeniusEquiv hCohomology) (A.integralDeRhamInclusion x) :=
  (LinearMap.congr_fun A.constructedIntegralFrobenius_inclusion x).trans
    (LinearMap.congr_fun (A.constructedDeRhamFrobenius_equiv hCohomology) (A.integralDeRhamInclusion x))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
