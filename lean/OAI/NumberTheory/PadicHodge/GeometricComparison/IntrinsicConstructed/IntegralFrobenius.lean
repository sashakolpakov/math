import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicConstructed.CrystallinePullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.DeRhamLattice
import OAI.NumberTheory.PadicHodge.GeometricComparison.TensorLatticeLinear

/-! # Integral Frobenius -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The constructed integral crystalline Frobenius intertwines the
original generic-fiber lattice inclusion with the constructed rational operator. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

def Geometry.AbelianH1Model.constructedDeRhamFrobenius : Module.End ℚ_[q] A.DeRham :=
  A.constructedCrystallineDeRhamEquiv.toLinearMap.comp
    (A.crystallineFrobenius.comp A.constructedCrystallineDeRhamEquiv.symm.toLinearMap)

theorem Geometry.AbelianH1Model.constructedIntegralFrobenius_inclusion :
    A.integralDeRhamInclusion.comp A.constructedIntegralFrobenius =
      (A.constructedDeRhamFrobenius.restrictScalars ℤ_[q]).comp A.integralDeRhamInclusion :=
  TensorLatticeLinear.TensorLatticeIntertwining.linearMap A.constructedRationalCrystallineEquiv A.integral_generic_deRham_hone
    A.crystallineFrobenius A.constructedIntegralFrobenius
    (A.constructedRationalCrystallineEquiv_pullback
      (AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod q) A.specialFiber.scheme))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
