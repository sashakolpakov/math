import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.GenericFiberOne
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
import Mathlib.RingTheory.Localization.BaseChange

/-! # De Rham Lattice -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The actual integral de Rham H-one embeds as a full finite free lattice in the original generic-fiber cohomology. -/

open scoped TensorProduct nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

instance Geometry.AbelianH1Model.deRhamIntegerModule : Module ℤ_[q] A.DeRham :=
  Module.compHom _ (algebraMap ℤ_[q] ℚ_[q])

instance Geometry.AbelianH1Model.deRhamIntegerTower : IsScalarTower ℤ_[q] ℚ_[q] A.DeRham where
  smul_assoc a b x := by
    change ((a : ℚ_[q]) * b) • x = (a : ℚ_[q]) • (b • x)
    exact mul_smul _ _ _

def Geometry.AbelianH1Model.integralDeRhamInclusion : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1 →ₗ[ℤ_[q]] A.DeRham :=
  (A.integral_generic_deRham_hone.toLinearMap.restrictScalars ℤ_[q]).comp
    (TensorProduct.mk ℤ_[q] ℚ_[q] (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1) 1)

theorem Geometry.AbelianH1Model.integralDeRhamInclusion_isBaseChange : IsBaseChange ℚ_[q] A.integralDeRhamInclusion :=
  (TensorProduct.isBaseChange ℤ_[q] (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1) ℚ_[q]).comp
    (IsBaseChange.ofEquiv A.integral_generic_deRham_hone)

instance Geometry.AbelianH1Model.integralDeRhamInclusion_localized : IsLocalizedModule ℤ_[q]⁰ A.integralDeRhamInclusion :=
  (isLocalizedModule_iff_isBaseChange ℤ_[q]⁰ ℚ_[q] A.integralDeRhamInclusion).mpr
    A.integralDeRhamInclusion_isBaseChange

theorem Geometry.AbelianH1Model.integralDeRhamInclusion_injective : Function.Injective A.integralDeRhamInclusion := by
  let := A.integral_deRham_hone_torsionFree
  apply (IsLocalizedModule.injective_iff_isRegular ℤ_[q]⁰ A.integralDeRhamInclusion).mpr
  intro s
  exact IsSMulRegular.of_ne_zero (nonZeroDivisors.coe_ne_zero s)

theorem Geometry.AbelianH1Model.integral_deRham_hone_finrank :
    Module.finrank ℤ_[q] (AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[q] A.integral.scheme 1) =
      Module.finrank ℚ_[q] A.DeRham := by
  rw [IsFractionRing.finrank_right_eq ℤ_[q] ℚ_[q] A.DeRham]
  exact (IsLocalizedModule.finrank_eq ℤ_[q]⁰ A.integralDeRhamInclusion le_rfl).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
