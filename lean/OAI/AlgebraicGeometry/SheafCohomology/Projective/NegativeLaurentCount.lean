import OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentWeightFinite
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Existence

/-! # Negative Laurent Count -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentCount

noncomputable section

/-! Full-negative Laurent exponents are counted by ordinary homogeneous monomials. -/

set_option backward.isDefEq.respectTransparency false
universe u
namespace MvPolynomial
open _root_.MvPolynomial
variable {σ : Type} [Fintype σ]

abbrev FullNegativeLaurentWeight (σ : Type) (d : ℤ) :=
  {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d // ∀ i, e.val i < 0}

def fullNegativeLaurentWeightEquivDegree (m : ℕ) :
    FullNegativeLaurentWeight σ (-(m : ℤ) - (Fintype.card σ : ℤ)) ≃
      {a : σ →₀ ℕ // Finsupp.degree a = m} where
  toFun e := ⟨Finsupp.equivFunOnFinite.symm (fun i => (-e.val.val i - 1).toNat), by
    have hcast (i : σ) : ((-e.val.val i - 1).toNat : ℤ) = -e.val.val i - 1 := by
      have := e.property i
      omega
    have hs : ∑ i, e.val.val i = -(m : ℤ) - (Fintype.card σ : ℤ) := by
      rw [← Finsupp.degree_eq_sum]
      exact e.val.property
    have hdeg : ((Finsupp.degree
        (Finsupp.equivFunOnFinite.symm (fun i => (-e.val.val i - 1).toNat)) : ℕ) : ℤ) = m := by
      rw [Finsupp.degree_eq_sum, Nat.cast_sum]
      simp only [Finsupp.equivFunOnFinite_symm_apply_apply, hcast]
      rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, hs]
      simp
    exact_mod_cast hdeg⟩
  invFun a := ⟨⟨Finsupp.equivFunOnFinite.symm (fun i => -(a.val i : ℤ) - 1), by
      rw [Finsupp.degree_eq_sum]
      simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
      rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Nat.cast_sum,
        ← Finsupp.degree_eq_sum, a.property]
      simp⟩, fun i => by
        change -(a.val i : ℤ) - 1 < 0
        omega⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    ext i
    change -((-e.val.val i - 1).toNat : ℤ) - 1 = e.val.val i
    have := e.property i
    omega
  right_inv a := by
    apply Subtype.ext
    ext i
    change (-(-(a.val i : ℤ) - 1) - 1).toNat = a.val i
    omega

def liftedFullNegativeLaurentWeightEquiv (d : ℤ) :
    {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ d //
      e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))} ≃ FullNegativeLaurentWeight σ d where
  toFun e := ⟨e.val, fun i => by
    have h : ULift.up i ∈ e.val.liftedNegativeSupport := by rw [e.property]; trivial
    exact h⟩
  invFun e := ⟨e.val, Set.eq_univ_of_forall (fun i => e.property i.down)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem fullNegativeLaurentWeight_card {r : ℕ} (m : ℕ) :
    Nat.card (FullNegativeLaurentWeight (Fin (r + 1)) (-(m : ℤ) - (r + 1 : ℕ))) =
      (m + r).choose r := by
  have he := Nat.card_congr (fullNegativeLaurentWeightEquivDegree (σ := Fin (r + 1)) m)
  simpa only [Fintype.card_fin] using
    he.trans (HilbertScheme.Presentations.Hilbert.Existence.GradedHilbert.card_degreeExponents r m)

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentCount
