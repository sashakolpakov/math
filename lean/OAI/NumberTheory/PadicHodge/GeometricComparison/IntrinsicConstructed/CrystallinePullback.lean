import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicConstructed.Crystalline
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallinePullbackCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.RationalizedConjugationPure

/-! # Crystalline Pullback -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! Transporting actual integral crystalline Frobenius through the
constructed comparison gives an integral operator with the required
rational intertwining. Hodge-step divisibility is a further obligation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

def Geometry.AbelianH1Model.transportedIntegralCrystallinePullback (g : A.specialFiber.scheme ⟶ A.specialFiber.scheme) :
    Module.End ℤ_[q] (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1) :=
  A.constructedIntegralCrystallineEquiv.symm.toLinearMap.comp
    ((IntrinsicPadic.CrystallinePullbackCoordinates.IntrinsicPadicCrystallinePullbackCoordinates.integral q g).comp A.constructedIntegralCrystallineEquiv.toLinearMap)

theorem Geometry.AbelianH1Model.transportedIntegralCrystallinePullback_equiv (g : A.specialFiber.scheme ⟶ A.specialFiber.scheme)
    (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1) :
    A.constructedIntegralCrystallineEquiv (A.transportedIntegralCrystallinePullback g x) =
      IntrinsicPadic.CrystallinePullbackCoordinates.IntrinsicPadicCrystallinePullbackCoordinates.integral q g (A.constructedIntegralCrystallineEquiv x) :=
  A.constructedIntegralCrystallineEquiv.apply_symm_apply _

theorem Geometry.AbelianH1Model.constructedRationalCrystallineEquiv_pullback (g : A.specialFiber.scheme ⟶ A.specialFiber.scheme)
    : A.constructedRationalCrystallineEquiv.toLinearMap.comp
        ((A.transportedIntegralCrystallinePullback g).baseChange ℚ_[q]) =
      (Crystalline.CoefficientAdapter.rationalPullback q g).comp A.constructedRationalCrystallineEquiv.toLinearMap :=
  RationalizedConjugationPure.RationalizedConjugation.linearMap ℚ_[q] A.constructedIntegralCrystallineEquiv
    (IntrinsicPadic.CrystallinePullbackCoordinates.IntrinsicPadicCrystallineScalarCoordinates.rationalEquiv q A.specialFiber.scheme)
    (IntrinsicPadic.CrystallinePullbackCoordinates.IntrinsicPadicCrystallinePullbackCoordinates.integral q g) (Crystalline.CoefficientAdapter.rationalPullback q g)
    (IntrinsicPadic.CrystallinePullbackCoordinates.IntrinsicPadicCrystallinePullbackCoordinates.rational q g)

def Geometry.AbelianH1Model.constructedIntegralFrobenius : Module.End ℤ_[q] (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1) :=
  A.transportedIntegralCrystallinePullback (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) A.specialFiber.scheme)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
