import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.Dimension
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.CrystallineDeterminantTransport
import OAI.NumberTheory.PadicHodge.GeometricComparison.SemilinearFiltrationT
import OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.CrystallineBoundedScalar
import OAI.NumberTheory.PadicHodge.IntegralComparison.Reference.CrystallineDeterminant

/-! # Bounded Degree Determinant -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! A degree action on the original bounded top cohomology gives
the determinant of the original rational H1 pullback. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] IntegralComparison.GradedExteriorCup.exteriorPowerCup
  PeriodInvariants.CrystallinePullback.rationalPullback

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  (j : K →+* ℂ)
  (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)

include j P

theorem Geometry.AbelianH1Model.native_small_crystalline_finrank :
    Module.finrank (FractionRing (WittVector q (ZMod q)))
      (IntegralComparison.Witt.Crystalline.rationalCohomology q (ZMod q) A.specialFiber.scheme 1) =
        2 * A.dimension := by
  let : FiniteDimensional ℚ_[q] A.Crystalline :=
    CrystallineDimension.FrobeniusSlope.crystalline_finite A j P
  exact (SemilinearFiltrationT.SemilinearFiltration.finrank (GeometricComparison.Crystalline.CoefficientAdapter.coefficientFieldEquiv q).symm
    (Integral.FrobeniusAdapter.CrystallineAdapter.nativeSmallToBigEquiv q A.specialFiber.scheme).symm).trans
      (A.native_crystalline_finrank j P)

theorem Geometry.AbelianH1Model.native_det_of_bounded_top_scalar
    (f : A.specialFiber.scheme ⟶ A.specialFiber.scheme) (d : ℕ)
    (hprod : IntegralComparison.GradedExteriorCup.exteriorPowerCup
      (IntegralComparison.Balanced.RationalCupUnit.data q (ZMod q) A.specialFiber.scheme
        A.specialFiber_projective) (2 * A.dimension) ≠ 0)
    (hscalar : ∀ (n : ℕ) (x : IntegralComparison.BoundedCrystalline.CrystallineCohomology.Cohomology (p := q)
      (J := Ideal.span {(q : WittVector q (ZMod q))})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers q (ZMod q))
      (IntegralComparison.Witt.Crystalline.wittStructureMap q (ZMod q) A.specialFiber.scheme) n
      (2 * A.dimension)),
      IntegralComparison.BoundedCrystalline.CrystallinePullback.pullback f.left
        (IntegralComparison.SmoothProper.WittGeometricRefinement.over_witt q (ZMod q)
          A.specialFiber.scheme A.specialFiber.scheme f) n (2 * A.dimension) x = d • x) :
    (GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q f).det = (d : ℚ_[q]) := by
  let : FiniteDimensional ℚ_[q] A.Crystalline :=
    CrystallineDimension.FrobeniusSlope.crystalline_finite A j P
  let : FiniteDimensional (FractionRing (WittVector q (ZMod q)))
      (IntegralComparison.Witt.Crystalline.rationalCohomology q (ZMod q) A.specialFiber.scheme 1) :=
    Intrinsic.CrystallineDeterminantTransport.CrystallineAdapter.nativeSmall_finite_of_big q (X := A.specialFiber.scheme)
  have hn := A.native_small_crystalline_finrank j P
  have hp : IntegralComparison.GradedExteriorCup.exteriorPowerCup
      (IntegralComparison.Balanced.RationalCupUnit.data q (ZMod q) A.specialFiber.scheme
        A.specialFiber_projective)
      (Module.finrank (FractionRing (WittVector q (ZMod q)))
        (IntegralComparison.Witt.Crystalline.rationalCohomology q (ZMod q) A.specialFiber.scheme 1)) ≠ 0 := by
    rw [hn]
    exact hprod
  have ht : ∀ x : IntegralComparison.Witt.Crystalline.rationalCohomology q (ZMod q) A.specialFiber.scheme
      (Module.finrank (FractionRing (WittVector q (ZMod q)))
        (IntegralComparison.Witt.Crystalline.rationalCohomology q (ZMod q) A.specialFiber.scheme 1)),
      PeriodInvariants.CrystallinePullback.rationalPullback q (ZMod q) f
        (Module.finrank (FractionRing (WittVector q (ZMod q)))
          (IntegralComparison.Witt.Crystalline.rationalCohomology q (ZMod q) A.specialFiber.scheme 1)) x =
        (d : FractionRing (WittVector q (ZMod q))) • x := by
    rw [hn]
    intro x
    rw [Nat.cast_smul_eq_nsmul]
    exact IntegralComparison.Reference.CrystallineBoundedScalar.rational_scalar q (ZMod q)
      A.specialFiber.scheme A.specialFiber_projective f (2 * A.dimension) d hscalar x
  have hd := IntegralComparison.Reference.CrystallineDeterminant.of_top_scalar q (ZMod q)
    A.specialFiber.scheme A.specialFiber_projective f
    (d : FractionRing (WittVector q (ZMod q))) hp ht
  rw [Intrinsic.CrystallineDeterminantTransport.CrystallineAdapter.nativeSmallToBigEquiv_det q f, hd, map_natCast]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
