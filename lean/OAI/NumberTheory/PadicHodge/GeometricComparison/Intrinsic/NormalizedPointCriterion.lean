import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.ScalarCriterion
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.ShiftTrace
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.FromTopDegree
import OAI.NumberTheory.PadicHodge.GeometricComparison.ProjectiveTarget
import OAI.NumberTheory.PadicHodge.GeometricComparison.CompletionIntrinsic

/-! # Normalized Point Criterion -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The genuine finite-level Serre trace supplies the degree formula.
The remaining point-class equality and top cup-product nonvanishing
then give the original shared polynomial and full comparison target. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] IntegralComparison.GradedExteriorCup.exteriorPowerCup

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

local instance Geometry.AbelianH1Model.normalizedPointCrystallineFree : Module.Free ℚ_[q] A.Crystalline :=
  Module.Free.of_divisionRing (K := ℚ_[q]) (V := A.Crystalline)

theorem Geometry.AbelianH1Model.truncatedShiftBounded_scalar_of_native_point
    (n m : ℕ) (hm : ¬q ∣ m) (hpos : 0 < A.dimension)
    (y : A.specialFiber.scheme.left)
    (hpoint : A.truncatedShiftCommonEdge n m hm
        ((A.truncatedShiftCommonTraceEquiv n m hm hpos).symm 1) =
      A.truncatedCrystallineTopEdge n
        ((A.truncatedSmallTopFormTraceEquiv n hpos).symm 1))
    (x : A.NativeBoundedCrystallineCohomology n (A.dimension + A.dimension)) :
    A.truncatedShiftBoundedPullback n m (A.dimension + A.dimension) x =
      (A.truncatedShiftSpecial m).finrank y • x :=
  A.truncatedShiftBounded_scalar_of_normalized_point n m hm hpos
    ((A.truncatedShiftSpecial m).finrank y)
    (A.truncatedShiftCommonTraceEquiv n m hm hpos) hpoint
    (A.truncatedShiftCommonTrace_pullback n m hm hpos y) x

variable (j : K →+* ℂ)
  (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)

include j P in
theorem Geometry.AbelianH1Model.native_crystalline_charpoly_of_normalized_points
    (hpos : 0 < A.dimension) (y : A.specialFiber.scheme.left)
    (hprod : IntegralComparison.GradedExteriorCup.exteriorPowerCup
      (IntegralComparison.Balanced.RationalCupUnit.data q (ZMod q) A.specialFiber.scheme
        A.specialFiber_projective) (2 * A.dimension) ≠ 0)
    (hpoint : ∀ (n m : ℕ) (hm : ¬q ∣ m),
      A.truncatedShiftCommonEdge n m hm
          ((A.truncatedShiftCommonTraceEquiv n m hm hpos).symm 1) =
        A.truncatedCrystallineTopEdge n
          ((A.truncatedSmallTopFormTraceEquiv n hpos).symm 1)) :
    letI : FiniteDimensional ℚ_[q] A.Crystalline :=
      CrystallineDimension.FrobeniusSlope.crystalline_finite A j P
    A.crystallineFrobenius.charpoly =
      A.nativeIntegerFrobeniusPolynomial.map (Int.castRingHom ℚ_[q]) := by
  apply A.native_crystalline_charpoly_of_bounded_shift_degrees j P y hprod
  intro m hm n
  rw [two_mul]
  exact A.truncatedShiftBounded_scalar_of_native_point n m hm hpos y (hpoint n m hm)

theorem Geometry.AbelianH1Model.projective_comparisonTarget_of_normalized_points
    {H : Type} [CommRing H] [Algebra ℚ H]
    (κ : K →+* AlgebraicClosure ℚ) (jComplex : AlgebraicClosure ℚ →+* ℂ)
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (hplace : (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq = ι.comp κ)
    (ρ : A.HeckeRealization H)
    (Q : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (jComplex.comp κ)).scheme.left
      (A.complexFiber (jComplex.comp κ)).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (hpos : 0 < A.dimension) (y : A.specialFiber.scheme.left)
    (hprod : IntegralComparison.GradedExteriorCup.exteriorPowerCup
      (IntegralComparison.Balanced.RationalCupUnit.data q (ZMod q) A.specialFiber.scheme
        A.specialFiber_projective) (2 * A.dimension) ≠ 0)
    (hpoint : ∀ (n m : ℕ) (hm : ¬q ∣ m),
      A.truncatedShiftCommonEdge n m hm
          ((A.truncatedShiftCommonTraceEquiv n m hm hpos).symm 1) =
        A.truncatedCrystallineTopEdge n
          ((A.truncatedSmallTopFormTraceEquiv n hpos).symm 1)) :
    HeckeScalar.ComparisonTarget q κ jComplex ι jq A H ρ Q ℓ := by
  let : FiniteDimensional ℚ_[q] A.Crystalline :=
    CrystallineDimension.FrobeniusSlope.crystalline_finite A (jComplex.comp κ) Q
  exact A.projective_comparisonTarget_of_shared_polynomial CompletionIntrinsic.nativeGeometricWeightInput
    κ jComplex ι hplace ρ Q ℓ hℓq A.nativeIntegerFrobeniusPolynomial
    (A.nativeIntegerFrobeniusPolynomial_isWeil ℓ hℓq)
    (A.native_crystalline_charpoly_of_normalized_points (jComplex.comp κ) Q hpos y hprod hpoint)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
