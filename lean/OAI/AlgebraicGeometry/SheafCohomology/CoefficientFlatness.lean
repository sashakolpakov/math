import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Coefficient Flatness -/

namespace OAI.AlgebraicGeometry.SheafCohomology.CoefficientFlatness.Projective

noncomputable section

/-! Exactness input for extension from integral to complex coefficients. -/

open _root_.CategoryTheory

/-- Extension of scalars along the actual inclusion of integers in the complex field. -/
abbrev extendComplexCoefficients : ModuleCat.{0} ℤ ⥤ ModuleCat.{0} ℂ :=
  ModuleCat.extendScalars (Int.castRingHom ℂ)

set_option backward.isDefEq.respectTransparency false in
/-- Complex coefficients are flat over the integers, so extension preserves injections. -/
instance extendComplexCoefficients_preservesMonos :
    extendComplexCoefficients.PreservesMonomorphisms where
  preserves {M N} f hf := by
    apply (ModuleCat.mono_iff_injective _).mpr
    change Function.Injective
      (@LinearMap.baseChange ℤ ℂ M N _ _
        ((algebraMap ℂ ℂ).comp (Int.castRingHom ℂ)).toAlgebra _ _ _ _ f.hom)
    rw [Subsingleton.elim
      ((algebraMap ℂ ℂ).comp (Int.castRingHom ℂ)).toAlgebra (inferInstance : Algebra ℤ ℂ)]
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := ℂ) f.hom
      ((ModuleCat.mono_iff_injective f).mp hf)

end

end OAI.AlgebraicGeometry.SheafCohomology.CoefficientFlatness.Projective
