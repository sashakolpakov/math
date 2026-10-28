import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentCount
import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentTop
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Negative Laurent Dimension -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective

noncomputable section

open _root_.MvPolynomial

/-! The dimension of top Laurent Čech cohomology is a binomial coefficient. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem NegativeLaurentDimension.MvPolynomial.coordinateHomogeneousLaurentTopHomology_finrank {r : ℕ}
    (j : Fin (r + 2)) (m : ℕ) (hfield : IsField Γ(Spec (CommRingCat.of R), ⊤)) :
    Module.finrank Γ(Spec (CommRingCat.of R), ⊤)
      ((TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j
        (-(m : ℤ) - (r + 2 : ℕ))).homology (r + 1)) =
          (m + (r + 1)).choose (r + 1) := by
  let := hfield.toField
  rw [(NegativeLaurentTop.MvPolynomial.coordinateHomogeneousLaurentTopHomologyEquivCoefficients (R := R) j
    (-(m : ℤ) - (r + 2 : ℕ)) r (by simp)).finrank_eq]
  let : Fintype {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent (Fin (r + 2)) (-(m : ℤ) - (r + 2 : ℕ)) //
      e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} (Fin (r + 2))))} :=
    (LaurentWeight.MvPolynomial.HomogeneousLaurentExponent.finite_setOf_liftedNegativeSupport_eq_univ
      (σ := Fin (r + 2)) (-(m : ℤ) - (r + 2 : ℕ))).fintype
  rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (NegativeLaurentCount.MvPolynomial.liftedFullNegativeLaurentWeightEquiv.{u}
    (σ := Fin (r + 2)) (-(m : ℤ) - (r + 2 : ℕ)))).trans
      (NegativeLaurentCount.MvPolynomial.fullNegativeLaurentWeight_card (r := r + 1) m)

theorem NegativeLaurentCount.MvPolynomial.FullNegativeLaurentWeight.degree_le {σ : Type} [Fintype σ] {d : ℤ}
    (e : NegativeLaurentCount.MvPolynomial.FullNegativeLaurentWeight σ d) : d ≤ -(Fintype.card σ : ℤ) := by
  have hsum : ∑ i, e.val.val i ≤ ∑ _i : σ, (-1 : ℤ) :=
    Finset.sum_le_sum (fun i _ => by have := e.property i; omega)
  rw [← Finsupp.degree_eq_sum, e.val.property] at hsum
  simpa using hsum

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective
