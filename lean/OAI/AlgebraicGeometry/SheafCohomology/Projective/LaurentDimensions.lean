import OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroNegative
import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentDimension
import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentVanishing

/-! # Laurent Dimensions -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentDimensions

noncomputable section

open _root_.MvPolynomial

/-! Dimension and vanishing formulas for projective Laurent Čech cohomology. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem coordinateHomogeneousLaurentHZero_finrank {r : ℕ}
    (j : Fin (r + 1)) (m : ℕ) (hfield : IsField Γ(Spec (CommRingCat.of R), ⊤)) :
    Module.finrank Γ(Spec (CommRingCat.of R), ⊤)
      ((TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j (m : ℤ)).homology 0) =
        (m + r).choose r := by
  let := hfield.toField
  let e := (DegreeZeroPolynomials.MvPolynomial.homogeneousLaurentHZeroLinearEquivCycles (R := R) j (m : ℤ)).trans
    (LaurentZeroCoefficients.MvPolynomial.laurentZeroCyclesEquivCoefficients (R := R) (m : ℤ) (Int.natCast_nonneg m) j)
  rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (NonnegativeLaurentPolynomials.MvPolynomial.nonnegativeLaurentWeightEquivDegree (σ := Fin (r + 1)) m)).trans
    (HilbertScheme.Presentations.Hilbert.Existence.GradedHilbert.card_degreeExponents r m)

theorem coordinateHomogeneousLaurentPositiveHomology_subsingleton_of_degree_gt
    {σ : Type} [Fintype σ] [LinearOrder σ] (j : σ) (d : ℤ) (n : ℕ)
    (hd : -(Fintype.card σ : ℤ) < d) :
    Subsingleton ((TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j d).homology (n + 1)) := by
  have : IsEmpty {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
      e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))} :=
    ⟨fun e => (not_le_of_gt hd) ((NegativeLaurentCount.MvPolynomial.liftedFullNegativeLaurentWeightEquiv.{u} d e).degree_le)⟩
  have : Subsingleton (LaurentExceptionalWeights.MvPolynomial.coordinateHomogeneousLaurentFullNegativeCochain.{u, u}
      (R := R) (σ := σ) d (n + 1)) := inferInstance
  exact ((NegativeLaurentHomology.MvPolynomial.coordinateHomogeneousLaurentPositiveHomologyEquivFullNegativeCycles (R := R) j d n).trans
    (NegativeLaurentTop.MvPolynomial.coordinateFullNegativeCyclesEquivCochain (R := R) d (n + 1))).injective.subsingleton

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentDimensions
