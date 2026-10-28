import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCechCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.CochainReduction

/-! # Integral Reduction Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralReductionCoordinates.IntrinsicPadicIntegralReductionCoordinates

noncomputable section

/-! Reduction on the same etale coordinate cover as the constructed
crystalline comparison detects exactly the prime multiples. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom]

local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X
local notation "C" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion.complex ℤ_[p] X U

def reduction (n : ℕ) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X 1 →ₗ[ℤ_[p]]
    CochainQuotientCohomology.PrincipalCochainQuotient.cohomology ℤ_[p] C (p : ℤ_[p]) n 1 :=
  (CochainQuotientCohomology.PrincipalCochainQuotient.reduction ℤ_[p] C (p : ℤ_[p]) n 1).comp
    (IntegralCechCoordinates.IntrinsicPadicIntegralCechCoordinates.equiv p X).toLinearMap

theorem zero_iff (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X 1) :
    reduction p X 1 x = 0 ↔ ∃ y, x = (p : ℤ_[p]) • y := by
  have hreg := IntegralFirst.ThreeCechRegularity.IntegralFirstThreeCechRegularity.total_regular ℤ_[p] X U
    (Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.affine ℤ_[p] X)
    (p : ℤ_[p]) (IsRegular.of_ne_zero (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))
  change CochainQuotientCohomology.PrincipalCochainQuotient.reduction ℤ_[p] C (p : ℤ_[p]) 1 1
    (IntegralCechCoordinates.IntrinsicPadicIntegralCechCoordinates.equiv p X x) = 0 ↔ _
  rw [CochainReduction.CochainReductionDivisibility.zero_iff ℤ_[p] C (p : ℤ_[p]) hreg]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(IntegralCechCoordinates.IntrinsicPadicIntegralCechCoordinates.equiv p X).symm y, ?_⟩
    apply (IntegralCechCoordinates.IntrinsicPadicIntegralCechCoordinates.equiv p X).injective
    simpa only [map_smul, LinearEquiv.apply_symm_apply] using hy.symm
  · rintro ⟨y, rfl⟩
    exact ⟨IntegralCechCoordinates.IntrinsicPadicIntegralCechCoordinates.equiv p X y,
      (map_smul (IntegralCechCoordinates.IntrinsicPadicIntegralCechCoordinates.equiv p X) (p : ℤ_[p]) y).symm⟩

theorem completion_eval (x : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.cohomology ℤ_[p] X 1) (n : ℕ) :
    (IntegralCechCoordinates.IntrinsicPadicIntegralCechCoordinates.completion p X x).val n = reduction p X n x :=
  IntegralCechCoordinates.IntrinsicPadicIntegralCechCoordinates.completion_eval p X x n

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralReductionCoordinates.IntrinsicPadicIntegralReductionCoordinates
