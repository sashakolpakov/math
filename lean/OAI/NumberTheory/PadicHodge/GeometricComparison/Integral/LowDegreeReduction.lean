import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.LowDegreeBaseChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.QuotientModule

/-! # Low Degree Reduction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.LowDegreeReduction.IntegralLowDegreeReduction

noncomputable section

/-! Reduction of the actual first two differential-form modules is surjective and has exactly the coefficient-ideal kernel. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation
open scoped TensorProduct Pointwise

universe u

variable (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]

theorem isBaseChange (n : ℕ) (hn : n ≤ 1) :
    IsBaseChange S (Forms.ScalarMap.FormsBaseChange.formExtensionMap R S A B n) := by
  have he : Function.Bijective (Forms.ScalarMap.FormsBaseChange.formScalarMap R S A B n) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
    · rw [← LowDegreeBaseChange.IntegralLowDegreeBaseChange.zero_eq_map]
      exact (LowDegreeBaseChange.IntegralLowDegreeBaseChange.zeroEquiv R S A B).bijective
    · rw [← LowDegreeBaseChange.IntegralLowDegreeBaseChange.one_eq_map]
      exact (LowDegreeBaseChange.IntegralLowDegreeBaseChange.oneEquiv R S A B).bijective
  let e := LinearEquiv.ofBijective (Forms.ScalarMap.FormsBaseChange.formScalarMap R S A B n) he
  apply IsBaseChange.of_equiv e
  intro ω
  change Forms.ScalarMap.FormsBaseChange.formScalarMap R S A B n (1 ⊗ₜ[R] ω) = _
  rw [Forms.ScalarMap.FormsBaseChange.formScalarMap_tmul, one_smul]

theorem surjective (n : ℕ) (hn : n ≤ 1) (hS : Function.Surjective (algebraMap R S)) :
    Function.Surjective (Forms.ScalarMap.FormsBaseChange.formExtensionMap R S A B n) :=
  QuotientModule.QuotientModuleBaseChange.surjective R S _ (isBaseChange R S A B n hn) hS

theorem ker_eq (n : ℕ) (hn : n ≤ 1) (hS : Function.Surjective (algebraMap R S)) :
    (Forms.ScalarMap.FormsBaseChange.formExtensionMap R S A B n).ker =
      RingHom.ker (algebraMap R S) • ⊤ :=
  QuotientModule.QuotientModuleBaseChange.ker_eq R S _ (isBaseChange R S A B n hn) hS

theorem zero_iff_divisible (n : ℕ) (hn : n ≤ 1)
    (hS : Function.Surjective (algebraMap R S)) (r : R)
    (hr : RingHom.ker (algebraMap R S) = Ideal.span {r}) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) :
    Forms.ScalarMap.FormsBaseChange.formExtensionMap R S A B n ω = 0 ↔ ∃ η : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n, r • η = ω := by
  change ω ∈ (Forms.ScalarMap.FormsBaseChange.formExtensionMap R S A B n).ker ↔ _
  rw [ker_eq R S A B n hn hS, hr, Submodule.ideal_span_singleton_smul]
  simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.LowDegreeReduction.IntegralLowDegreeReduction
