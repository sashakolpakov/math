import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.LocalUnitary
import OAI.NumberTheory.Quaternion.Arithmetic.FiniteAdelicComparison

/-! # Finite Unitary -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.FiniteUnitary

noncomputable section

/-! The continuous map from the actual finite adelic quaternion group
to the restricted product of its diagonal special unitary subgroups. -/

open scoped Classical _root_.NumberField
open OAI.NumberTheory.Quaternion.Arithmetic.FiniteAdelicComparison
open OAI.RepresentationTheory.Theta.Adelic.IntegralTopology

variable (F : Type) [Field F] [NumberField F] (a b : F)

abbrev DiagonalFiniteSU := RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.RestrictedGroup
  (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
    RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F (UnitaryMatrixEquiv.Quadratic.diagonalForm (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) b)) (.inr v))

def quaternionFiniteUnitary :
    NumberTheory.Quaternion.Arithmetic.FiniteAdelicMatrices.FiniteAdelicGroupPoints (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)) →ₜ* DiagonalFiniteSU F a b :=
  RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.restrictedContinuousMap
    (fun v => NumberTheory.Quaternion.Arithmetic.LocalAdeles.integralLocalSubgroup (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)) (.inr v))
    (fun v => RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F (UnitaryMatrixEquiv.Quadratic.diagonalForm (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) b)) (.inr v))
    (LocalUnitary.quaternionLocalUnitaryContinuous F a b)
    (LocalUnitary.quaternionLocalUnitary_eventually_integral F a b)

theorem quaternionFiniteUnitary_apply
    (g : NumberTheory.Quaternion.Arithmetic.FiniteAdelicMatrices.FiniteAdelicGroupPoints (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)))
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    quaternionFiniteUnitary F a b g v = LocalUnitary.quaternionLocalUnitary F a b v (g v) := rfl

theorem quaternionFiniteUnitary_includePlace
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (g : NumberTheory.Quaternion.Arithmetic.LocalAdeles.LocalPoints (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)) (.inr v)) :
    quaternionFiniteUnitary F a b
      (RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace (fun w => NumberTheory.Quaternion.Arithmetic.LocalAdeles.integralLocalSubgroup (NumberTheory.Quaternion.Arithmetic.MatrixGroup.quaternionNormOneMatrixGroup a (-b)) (.inr w)) v g) =
    RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace (fun w => RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral F
      (UnitaryMatrixEquiv.Quadratic.diagonalForm (algebraMap F (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F a) b)) (.inr w)) v
      (LocalUnitary.quaternionLocalUnitary F a b v g) := by
  apply RestrictedProduct.ext
  intro w
  rw [quaternionFiniteUnitary_apply]
  by_cases hw : w = v
  · subst w
    rw [RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace_same, RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace_same]
  · rw [RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace_other _ hw, map_one, RepresentationTheory.Weil.AdelicSplitting.RestrictedLimits.Construction.includePlace_other _ hw]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Quaternion.FiniteUnitary
