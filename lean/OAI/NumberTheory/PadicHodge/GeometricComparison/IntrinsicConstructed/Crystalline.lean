import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCrystallineRational
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.GenericFiberOne
import OAI.NumberTheory.PadicHodge.GeometricComparison.SpecialFiberProjectivity
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AbelianReductionSequence

/-! # Crystalline -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicConstructed.Crystalline.AbelianModel

noncomputable section

/-! The integral tower construction and original generic-fiber map give
a comparison between the independently defined GeometricComparison cohomology spaces.
Operator compatibility and admissibility are separate assertions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

local instance _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.integral_scheme_separated : A.integral.scheme.left.IsSeparated := ⟨by
  rw [← terminal.comp_from A.integral.scheme.hom]
  infer_instance⟩

local notation "I" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.BoundedResolution.Comparison.resolution (p := q)
  (J := Ideal.span {(q : WittVector q (ZMod q))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers q (ZMod q))
  (IntegralComparison.Witt.Crystalline.wittStructureMap q (ZMod q) A.specialFiber.scheme)

def _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.constructedIntegralCrystallineEquiv : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1 ≃ₗ[ℤ_[q]]
    IntrinsicPadic.CrystallinePullbackCoordinates.IntrinsicPadicCrystallineScalarCoordinates.integral q A.specialFiber.scheme :=
  IntrinsicPadic.IntegralCrystallineEquiv.IntrinsicPadicIntegralCrystallineEquiv.equiv q A.integral.scheme A.specialFiber.scheme
    A.integralReductionMorphism A.integralReductionSquare I A.specialFiber_projective

def _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.constructedRationalCrystallineEquiv : ℚ_[q] ⊗[ℤ_[q]] AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1 ≃ₗ[ℚ_[q]]
    A.Crystalline :=
  IntrinsicPadic.IntegralCrystallineRational.IntrinsicPadicIntegralCrystallineRational.equiv q A.integral.scheme A.specialFiber.scheme
    A.integralReductionMorphism A.integralReductionSquare I A.specialFiber_projective

def _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.constructedCrystallineDeRhamEquiv : A.Crystalline ≃ₗ[ℚ_[q]] A.DeRham :=
  A.constructedRationalCrystallineEquiv.symm.trans A.integral_generic_deRham_hone

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicConstructed.Crystalline.AbelianModel
