import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriodNaturality

/-! # Tate Integral Span -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.TateIntegralSpan

noncomputable section

/-! The integral image of the actual Tate module is the span of the
literal integral native period labels under the canonical comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriodNaturality
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

variable (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (q : ℕ) [Fact q.Prime]

theorem native_integralTateImage_eq_period_span :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.integralTateImage A.toOver (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)) q =
      Submodule.span ℤ_[q] (Set.range fun x : AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A =>
        AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.rationalPeriodTateEquiv A q (1 ⊗ₜ[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.integralPeriodInclusion A x)) := by
  apply le_antisymm
  · rintro y ⟨t, rfl⟩
    obtain ⟨z, rfl⟩ := (AlgebraicGeometry.AbelianScheme.TateComparison.IntrinsicPeriod.nativeCompletedPeriodTateEquiv q A).surjective t
    change (1 : ℚ_[q]) ⊗ₜ[ℤ_[q]] AlgebraicGeometry.AbelianScheme.TateComparison.IntrinsicPeriod.nativeCompletedPeriodTateEquiv q A z ∈ _
    induction z using TensorProduct.inductionOn with
    | tmul a x =>
      rw [AlgebraicGeometry.AbelianScheme.TateComparison.IntrinsicPeriod.nativeCompletedPeriodTateEquiv_tmul, TensorProduct.tmul_smul]
      apply Submodule.smul_mem
      have h := Submodule.subset_span (R := ℤ_[q])
        (Set.mem_range_self (f := fun x : AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A =>
          AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.rationalPeriodTateEquiv A q (1 ⊗ₜ[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.integralPeriodInclusion A x)) x)
      rw [AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriodNaturality.rationalPeriodTateEquiv_tmul_integral, AlgebraicGeometry.AbelianScheme.TateComparison.IntrinsicPeriod.nativeCompletedPeriodTateEquiv_tmul, one_smul] at h
      exact h
    | add z w hz hw =>
      rw [map_add, TensorProduct.tmul_add]
      exact Submodule.add_mem _ hz hw
  · apply Submodule.span_le.mpr
    rintro y ⟨x, rfl⟩
    change AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.rationalPeriodTateEquiv A q (1 ⊗ₜ[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriod.integralPeriodInclusion A x) ∈ _
    rw [AlgebraicGeometry.AbelianScheme.TateComparison.RationalPeriodNaturality.rationalPeriodTateEquiv_tmul_integral]
    exact ⟨AlgebraicGeometry.AbelianScheme.TateComparison.IntrinsicPeriod.nativeCompletedPeriodTateEquiv q A (1 ⊗ₜ[ℤ] x), rfl⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.TateIntegralSpan
