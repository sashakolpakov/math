import OAI.NumberTheory.PadicHodge.GeometricComparison.SinglePrime
import OAI.NumberTheory.PadicHodge.GeometricComparison.First.ZeroQuotient
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.DeRhamOne

/-! # Functions One -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.FunctionsOne.AbelianModel

noncomputable section

/-! Degree-one cohomology of the actual integral zero-form sheaf is torsion-free. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

local instance : Algebra ℤ_[q] (ZMod q) := PadicInt.toZMod.toAlgebra

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.integral_functions_hone_torsionFree :
    Module.IsTorsionFree ℤ_[q]
      ((DerivedCategory.singleFunctor (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.Sheaves ℤ_[q] A.integral.scheme) 0).obj
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.coefficientSheaf ℤ_[q] A.integral.scheme) ⟶
      (DerivedCategory.Q.obj ((First.ZeroQuotient.FirstZeroComplex.complex
        (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.sheafComplex ℤ_[q] A.integral.scheme)).extend
          ComplexShape.embeddingUpNat))⟦(1 : ℤ)⟧) := by
  let r := ReductionComplex.IntrinsicIntegralReductionComplex.sheafMap ℤ_[q] (ZMod q)
    A.integral.scheme A.specialFiber.scheme A.integralReductionMorphism A.integralReductionSquare.w
  have hz := ReductionSequence.IntrinsicIntegralReductionSequence.sheaf_zero ℤ_[q] (ZMod q)
    A.integral.scheme A.specialFiber.scheme A.integralReductionMorphism A.integralReductionSquare.w
    (q : ℤ_[q]) (Geometry.AbelianH1Model.residue_prime_zero (q := q))
  apply SinglePrime.SinglePrimeTorsion.torsionFree q A.integral.scheme.left _ _ (r.f 0)
    (congrArg (fun a => a.f 0) hz)
  · exact ReductionSequence.IntrinsicIntegralReductionSequence.low_shortExact ℤ_[q] (ZMod q)
      A.integral.scheme A.specialFiber.scheme A.integralReductionMorphism A.integralReductionSquare.w
      (q : ℤ_[q]) (Geometry.AbelianH1Model.residue_prime_zero (q := q)) A.integralReductionSquare
      (ZMod.ringHom_surjective PadicInt.toZMod)
      (PadicInt.ker_toZMod.trans PadicInt.maximalIdeal_eq_span_p)
      (IsRegular.of_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)) 0 (by omega)
  · exact ReductionZero.IntrinsicIntegralReductionHZero.zero_sections_surjective ℤ_[q] (ZMod q)
      A.integral.scheme A.specialFiber.scheme A.integralReductionMorphism A.integralReductionSquare.w
      A.specialFiber_functions_surjective

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.FunctionsOne.AbelianModel
