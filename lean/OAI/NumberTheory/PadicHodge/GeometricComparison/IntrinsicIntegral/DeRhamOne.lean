import OAI.NumberTheory.PadicHodge.GeometricComparison.First.TwoPrimeTorsion
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.ReductionSequence
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.ReductionZero
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.AbelianReductionSequence
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.Functions

/-! # De Rham One -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.DeRhamOne.AbelianModel

noncomputable section

/-! The native integral de Rham H-one of the actual abelian model has no prime torsion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

local instance : Algebra ℤ_[q] (ZMod q) := PadicInt.toZMod.toAlgebra

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.integral_deRham_hone_torsionFree :
    Module.IsTorsionFree ℤ_[q] (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1) := by
  let := A.integral_functions_isIso
  let r := ReductionComplex.IntrinsicIntegralReductionComplex.sheafMap ℤ_[q] (ZMod q)
    A.integral.scheme A.specialFiber.scheme A.integralReductionMorphism A.integralReductionSquare.w
  apply First.TwoPrimeTorsion.FirstTwoComplex.torsionFree q A.integral.scheme.left
    (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex ℤ_[q] A.integral.scheme)
    (ReductionComplex.IntrinsicIntegralReductionComplex.sheafComplex ℤ_[q] (ZMod q)
      A.integral.scheme A.specialFiber.scheme A.integralReductionMorphism) r
    (ReductionSequence.IntrinsicIntegralReductionSequence.sheaf_zero ℤ_[q] (ZMod q)
      A.integral.scheme A.specialFiber.scheme A.integralReductionMorphism A.integralReductionSquare.w
      (q : ℤ_[q]) (Geometry.AbelianH1Model.residue_prime_zero (q := q)))
  · intro n hn
    apply ReductionSequence.IntrinsicIntegralReductionSequence.low_shortExact ℤ_[q] (ZMod q)
      A.integral.scheme A.specialFiber.scheme A.integralReductionMorphism A.integralReductionSquare.w
      (q : ℤ_[q]) (Geometry.AbelianH1Model.residue_prime_zero (q := q)) A.integralReductionSquare
      (ZMod.ringHom_surjective PadicInt.toZMod)
    · exact PadicInt.ker_toZMod.trans PadicInt.maximalIdeal_eq_span_p
    · exact IsRegular.of_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
    · exact hn
  · apply ReductionZero.IntrinsicIntegralReductionHZero.zero_sections_surjective ℤ_[q] (ZMod q)
      A.integral.scheme A.specialFiber.scheme A.integralReductionMorphism A.integralReductionSquare.w
    exact A.specialFiber_functions_surjective
  · exact Integral.GlobalDifferential.IntegralGlobalDifferential.sheaf_differential_zero ℤ_[q] A.integral.scheme

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.DeRhamOne.AbelianModel
