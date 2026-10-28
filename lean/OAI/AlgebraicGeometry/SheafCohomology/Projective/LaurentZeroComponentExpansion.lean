import OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroComponentCoefficients

/-! # Laurent Zero Component Expansion -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroComponentExpansion

noncomputable section

/-! Every chart component of a nonnegative-degree Laurent zero cycle has its global monomial expansion. -/

set_option backward.isDefEq.respectTransparency false
open _root_.AlgebraicGeometry
universe u
namespace MvPolynomial
open _root_.MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]

theorem laurentZeroComponent_eq_sum (n : ℕ) (j : σ)
    (z : LaurentZeroCycleWeights.MvPolynomial.LaurentZeroCycles (R := R) (σ := σ) (n : ℤ))
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) 0) :
    LaurentCoordinates.MvPolynomial.homogeneousLaurentZeroComponent (n : ℤ) z a =
      ∑ e : LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (n : ℤ),
        AddMonoidAlgebra.single (PolynomialChartMap.MvPolynomial.nonnegativeLaurentWeightAllowed (fun k => (a.val k).down) n e)
          (LaurentZeroCoefficients.MvPolynomial.laurentZeroCoefficients (R := R) (n : ℤ) j z e) := by
  classical
  ext e
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  by_cases he : ∀ i, 0 ≤ e.val.val i
  · let w : LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (n : ℤ) := ⟨e.val, he⟩
    have hw : PolynomialChartMap.MvPolynomial.nonnegativeLaurentWeightAllowed (fun k => (a.val k).down) n w = e :=
      Subtype.ext rfl
    rw [← hw, LaurentZeroComponentCoefficients.MvPolynomial.laurentZeroComponent_coeff_nonnegative n j z a w]
    rw [Finset.sum_eq_single w]
    · simp
    · intro v _ hv
      have hne : PolynomialChartMap.MvPolynomial.nonnegativeLaurentWeightAllowed (fun k => (a.val k).down) n v ≠
          PolynomialChartMap.MvPolynomial.nonnegativeLaurentWeightAllowed (fun k => (a.val k).down) n w := by
        intro h
        have hval := congrArg (fun t : {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ (n : ℤ) //
          e.IsAllowedOn (fun k => (a.val k).down)} => t.val) h
        exact hv (Subtype.ext hval)
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_eq_right hne]
    · simp
  · rw [LaurentZeroComponentCoefficients.MvPolynomial.laurentZeroComponent_coeff_negative n j z a e he]
    symm
    apply Finset.sum_eq_zero
    intro w _
    have hne : PolynomialChartMap.MvPolynomial.nonnegativeLaurentWeightAllowed (fun k => (a.val k).down) n w ≠ e := by
      intro h
      apply he
      have hw : w.val = e.val := congrArg Subtype.val h
      rw [← hw]
      exact w.property
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_eq_right hne]

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroComponentExpansion
