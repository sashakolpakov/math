import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FlatPreimmersionReduced
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Base
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Generic Reduced -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel

noncomputable section

/-! The actual generic fiber of a reduced arithmetic model is reduced;
no replacement by its reduction is needed for the generic comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.NumberField

variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
    (B : Base.ArithmeticBaseExtension K κ)

theorem Base.ArithmeticBaseExtension.generic_preimmersion_flat : IsPreimmersion B.generic ∧ Flat B.generic := by
  let a := Spec.map (CommRingCat.ofHom (algebraMap (𝓞 B.extension.carrier) B.R))
  let g := Spec.map (CommRingCat.ofHom (algebraMap (𝓞 B.extension.carrier) B.extension.carrier))
  have ha : IsOpenImmersion a := inferInstanceAs (IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 B.extension.carrier) B.R))))
  have hg : IsPreimmersion g := IsPreimmersion.of_isLocalization
    (nonZeroDivisors (𝓞 B.extension.carrier))
  have he : B.generic ≫ a = g := by
    rw [Base.ArithmeticBaseExtension.generic, ← Spec.map_comp]
    apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    ext x
    exact ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField_algebraMap B.extension.carrier B.denominator B.denominator_ne_zero x
  have : IsPreimmersion (B.generic ≫ a) := he.symm ▸ hg
  refine ⟨IsPreimmersion.of_comp B.generic a, ?_⟩
  let : Algebra B.R B.extension.carrier := B.toField.toAlgebra
  have : IsScalarTower (𝓞 B.extension.carrier) B.R B.extension.carrier :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      (ArithmeticGeometry.Models.Algebra.Constructions.Foundations.integersAwayToField_algebraMap B.extension.carrier B.denominator B.denominator_ne_zero x).symm)
  have hflat : Module.Flat B.R B.extension.carrier :=
    (Module.flat_iff_of_isLocalization B.R (Submonoid.powers (B.denominator : 𝓞 B.extension.carrier))
      B.extension.carrier).mpr
        (IsLocalization.flat B.extension.carrier (nonZeroDivisors (𝓞 B.extension.carrier)))
  exact Flat.SpecMap_iff.mpr hflat

theorem Base.ArithmeticBaseExtension.genericFiber_isReduced (X : Over B.base) [IsReduced X.left] :
    IsReduced ((Over.pullback B.generic).obj X).left := by
  have := (Base.ArithmeticBaseExtension.generic_preimmersion_flat B).1
  have := (Base.ArithmeticBaseExtension.generic_preimmersion_flat B).2
  exact FlatPreimmersionReduced.flat_preimmersion_isReduced (CategoryTheory.Limits.pullback.fst X.hom B.generic)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel
