import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TwistResidueCoordinates
import OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroNegative
import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentVanishing

/-! # Negative Twist Vanishing -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.NegativeTwistVanishing

noncomputable section

/-! The original ordered Čech complex of a negative projective twist has
cohomology only in the top projective degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.TwistResidueCoordinates

universe u

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ] [Nontrivial σ]

attribute [local instance] MvPolynomial.gradedAlgebra

theorem subsingleton_homology (j : σ) (d : ℤ) (hd : d < 0) (n : ℕ)
    (hn : n + 1 ≠ Fintype.card σ) :
    Subsingleton ((TwistResidueCoordinates.complex (R := R) j d).homology n) := by
  have h : Subsingleton ((AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).homology n) := by
    cases n with
    | zero => exact AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroNegative.MvPolynomial.homogeneousLaurentHZero_subsingleton_of_neg (R := R) j d hd
    | succ q =>
      exact AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentVanishing.MvPolynomial.coordinateHomogeneousLaurentPositiveHomology_subsingleton_of_card_ne
        (R := R) (σ := σ) j d q hn
  exact (HomologicalComplex.homologyMapIso (TwistResidueCoordinates.laurentIso (R := R) j d) n).toLinearEquiv.injective.subsingleton

theorem isZero_homology (j : σ) (d : ℤ) (hd : d < 0) (n : ℕ)
    (hn : n + 1 ≠ Fintype.card σ) :
    Limits.IsZero ((TwistResidueCoordinates.complex (R := R) j d).homology n) := by
  let := subsingleton_homology (R := R) j d hd n hn
  exact ModuleCat.isZero_of_subsingleton _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.NegativeTwistVanishing
