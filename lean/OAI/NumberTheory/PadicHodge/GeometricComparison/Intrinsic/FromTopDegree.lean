import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.BoundedDegreeDeterminant
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.CrystallinePolynomialCriterion
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.FrobeniusShiftDegree

/-! # From Top Degree -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The remaining geometric degree calculation supplies the original
crystalline characteristic polynomial and its independently specified
étale Weil polynomial. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] IntegralComparison.GradedExteriorCup.exteriorPowerCup

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

local instance Geometry.AbelianH1Model.crystalline_free : Module.Free ℚ_[q] A.Crystalline :=
  Module.Free.of_divisionRing (K := ℚ_[q]) (V := A.Crystalline)

theorem Geometry.AbelianH1Model.nativeIntegerFrobeniusPolynomial_isWeil (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    A.IsWeilPolynomial ℓ A.nativeIntegerFrobeniusPolynomial := by
  refine ⟨A.native_etale_finite ℓ hℓq, ?_⟩
  exact A.native_etale_charpoly_eq_integer ℓ hℓq

variable (j : K →+* ℂ)
  (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)

include j P in
theorem Geometry.AbelianH1Model.native_crystalline_charpoly_of_bounded_shift_degrees
    (x : A.specialFiber.scheme.left)
    (hprod : IntegralComparison.GradedExteriorCup.exteriorPowerCup
      (IntegralComparison.Balanced.RationalCupUnit.data q (ZMod q) A.specialFiber.scheme
        A.specialFiber_projective) (2 * A.dimension) ≠ 0)
    (hscalar : ∀ (m : ℕ), ¬q ∣ m → ∀ (n : ℕ)
      (y : IntegralComparison.BoundedCrystalline.CrystallineCohomology.Cohomology (p := q)
        (J := Ideal.span {(q : WittVector q (ZMod q))})
        (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers q (ZMod q))
        (IntegralComparison.Witt.Crystalline.wittStructureMap q (ZMod q) A.specialFiber.scheme) n
        (2 * A.dimension)),
      IntegralComparison.BoundedCrystalline.CrystallinePullback.pullback
        (((m : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.specialFiber.scheme) +
          AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) A.specialFiber.scheme).toMul.hom.hom.left)
        (IntegralComparison.SmoothProper.WittGeometricRefinement.over_witt q (ZMod q)
          A.specialFiber.scheme A.specialFiber.scheme
          (((m : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.specialFiber.scheme) +
            AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) A.specialFiber.scheme).toMul.hom.hom))
        n (2 * A.dimension) y =
          (((m : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.specialFiber.scheme) +
            AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) A.specialFiber.scheme).toMul.hom.hom.left.finrank x) • y) :
    letI : FiniteDimensional ℚ_[q] A.Crystalline :=
      CrystallineDimension.FrobeniusSlope.crystalline_finite A j P
    A.crystallineFrobenius.charpoly =
      A.nativeIntegerFrobeniusPolynomial.map (Int.castRingHom ℚ_[q]) := by
  apply A.native_crystalline_charpoly_of_plus_pullback_determinants j P 0
  intro m _ hm
  rw [A.nativeIntegerFrobeniusPolynomial_eval_neg_nat_finrank m hm x, Int.cast_natCast]
  exact A.native_det_of_bounded_top_scalar j P
    (((m : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.specialFiber.scheme) +
      AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) A.specialFiber.scheme).toMul.hom.hom)
    (((m : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.specialFiber.scheme) +
      AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) A.specialFiber.scheme).toMul.hom.hom.left.finrank x)
    hprod (hscalar m hm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
