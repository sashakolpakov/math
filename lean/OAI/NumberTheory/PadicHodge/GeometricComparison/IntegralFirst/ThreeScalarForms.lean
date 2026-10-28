import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.TwoFormsBaseChange

/-! # Three Scalar Forms -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeScalarForms.IntegralFirstThreeScalarForms

noncomputable section

/-! The canonical flat coefficient map is an isomorphism on native forms through degree two. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation
open scoped TensorProduct

universe u

variable (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B] [Module.Flat R S]

theorem bijective (n : ℕ) (hn : n ≤ 2) :
    Function.Bijective (Forms.ScalarMap.FormsBaseChange.formScalarMap R S A B n) := by
  rcases n with _ | (_ | (_ | n))
  · rw [← Integral.LowDegreeBaseChange.IntegralLowDegreeBaseChange.zero_eq_map]
    exact (Integral.LowDegreeBaseChange.IntegralLowDegreeBaseChange.zeroEquiv R S A B).bijective
  · rw [← Integral.LowDegreeBaseChange.IntegralLowDegreeBaseChange.one_eq_map]
    exact (Integral.LowDegreeBaseChange.IntegralLowDegreeBaseChange.oneEquiv R S A B).bijective
  · rw [← Integral.TwoFormsBaseChange.IntegralTwoFormsBaseChange.scalarEquiv_eq_map]
    exact (Integral.TwoFormsBaseChange.IntegralTwoFormsBaseChange.scalarEquiv R S A B).bijective
  · omega

def equiv (n : ℕ) (hn : n ≤ 2) : S ⊗[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n ≃ₗ[S] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form S B n :=
  LinearEquiv.ofBijective (Forms.ScalarMap.FormsBaseChange.formScalarMap R S A B n) (IntegralFirstThreeScalarForms.bijective R S A B n hn)

theorem equiv_eq_map (n : ℕ) (hn : n ≤ 2) :
    (equiv R S A B n hn).toLinearMap = Forms.ScalarMap.FormsBaseChange.formScalarMap R S A B n := rfl

theorem equiv_symbol (n : ℕ) (hn : n ≤ 2) (s : S) (a : A) (v : Fin n → A) :
    equiv R S A B n hn (s ⊗ₜ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S B (algebraMap S B s * algebraMap A B a) (fun i => algebraMap A B (v i)) :=
  Forms.ScalarMap.FormsBaseChange.formScalarMap_symbol R S A B s a v

theorem differential (n : ℕ) (hn : n ≤ 1) (x : S ⊗[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    equiv R S A B (n + 1) (by omega) ((AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential R A n).baseChange S x) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.differential S B n (equiv R S A B n (by omega) x) :=
  Forms.ScalarMap.FormsBaseChange.formScalarMap_differential R S A B n x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeScalarForms.IntegralFirstThreeScalarForms
