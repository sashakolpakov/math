import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.ChosenCoverNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.DeRhamLattice
import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeScalar

/-! # Generic Fiber Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The existing original integral generic-fiber comparison and full lattice
inclusion commute with every actual extending endomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

def Geometry.AbelianH1Model.integralDeRhamPullback (f : A.ExtendingEndomorphism) :
    Module.End ℤ_[q] (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1) :=
  DeRham.Int.pullback f.integral.toMul.hom.hom 1

theorem Geometry.AbelianH1Model.integralGenericEndomorphism_square (f : A.ExtendingEndomorphism) :
    A.integralGenericMorphism ≫ f.integral.toMul.hom.hom.left =
      (A.localEndomorphism f).left ≫ A.integralGenericMorphism :=
  (pullback.lift_fst _ _ _).symm

theorem Geometry.AbelianH1Model.integral_generic_deRham_hone_naturality (f : A.ExtendingEndomorphism)
    (x : ℚ_[q] ⊗[ℤ_[q]] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1) :
    A.integral_generic_deRham_hone ((A.integralDeRhamPullback f).baseChange ℚ_[q] x) =
      A.deRhamPullback f (A.integral_generic_deRham_hone x) :=
  Integral.ChosenCoverNaturality.IntegralGlobalHOneBaseChange.quasiCompactEquiv_naturality ℤ_[q] ℚ_[q]
    f.integral.toMul.hom.hom (A.localEndomorphism f) A.integralGenericMorphism A.integralGenericMorphism
    A.integralGenericSquare A.integralGenericSquare (A.integralGenericEndomorphism_square f) x

theorem Geometry.AbelianH1Model.integralDeRhamInclusion_naturality (f : A.ExtendingEndomorphism)
    (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1) :
    A.integralDeRhamInclusion (A.integralDeRhamPullback f x) =
      A.deRhamPullback f (A.integralDeRhamInclusion x) := by
  have h := A.integral_generic_deRham_hone_naturality f ((1 : ℚ_[q]) ⊗ₜ[ℤ_[q]] x)
  rw [LinearMap.baseChange_tmul] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
