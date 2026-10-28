import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.GlobalOneBaseChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.DeRhamFiniteFree

/-! # Generic Fiber One -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The finite free integral de Rham H-one of the original abelian model spans its actual generic-fiber cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open scoped TensorProduct

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

def Geometry.AbelianH1Model.integralGenericMorphism : A.localFiber.scheme.left ⟶ A.integral.scheme.left :=
  pullback.fst A.integral.scheme.hom (Geometry.scalarBaseMap (algebraMap ℤ_[q] ℚ_[q]))

theorem Geometry.AbelianH1Model.integralGenericSquare :
    IsPullback A.integralGenericMorphism A.localFiber.scheme.hom A.integral.scheme.hom
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ_[q] ℚ_[q]))) :=
  IsPullback.of_hasPullback _ _

def Geometry.AbelianH1Model.integral_generic_deRham_hone :
    ℚ_[q] ⊗[ℤ_[q]] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1 ≃ₗ[ℚ_[q]] A.DeRham :=
  Integral.GlobalOneBaseChange.IntegralGlobalHOneBaseChange.quasiCompactEquiv ℤ_[q] A.integral.scheme ℚ_[q]
    A.localFiber.scheme A.integralGenericMorphism A.integralGenericSquare

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
