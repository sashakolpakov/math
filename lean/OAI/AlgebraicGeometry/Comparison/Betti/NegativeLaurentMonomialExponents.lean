import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentTop
import OAI.AlgebraicGeometry.Comparison.Betti.NormalizedPolynomialSupports

/-! # Negative Laurent Monomial Exponents -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.NegativeLaurentMonomialExponents.Dolbeault

noncomputable section

/-! The original algebraic full-negative Laurent weights are the positive exponents of normalized polynomials. -/

open scoped BigOperators

def positiveMonomialExponent (ι : Type) (k : ℕ) :=
  {e : ι →₀ ℕ // e.degree = k ∧ ∀ i, 0 < e i}

def fullNegativeMonomialExponent (ι : Type) (k : ℕ) :=
  {e : SheafCohomology.Projective.LaurentWeight.MvPolynomial.HomogeneousLaurentExponent ι (-(k : ℤ)) //
    e.liftedNegativeSupport = (Set.univ : Set (ULift.{0} ι))}

variable {ι : Type} [Fintype ι]

omit [Fintype ι] in
theorem fullNegativeMonomialExponent_lt (k : ℕ) (e : fullNegativeMonomialExponent ι k) (i : ι) :
    e.val.val i < 0 := by
  have h : ULift.up i ∈ e.val.liftedNegativeSupport := by rw [e.property]; trivial
  exact h

def positiveToNegativeMonomialExponent (k : ℕ) (e : positiveMonomialExponent ι k) :
    fullNegativeMonomialExponent ι k := by
  let v : ι →₀ ℤ := Finsupp.mapRange (fun n : ℕ => -(n : ℤ)) (by simp) e.val
  have hv : v.degree = -(k : ℤ) := by
    have he : (∑ i : ι, e.val i) = k := (Finsupp.degree_eq_sum e.val).symm.trans e.property.1
    simp only [Finsupp.degree_eq_sum, v, Finsupp.mapRange_apply, Finset.sum_neg_distrib,
      ← Nat.cast_sum, he]
  refine ⟨⟨v, hv⟩, Set.eq_univ_of_forall ?_⟩
  intro i
  change -(e.val i.down : ℤ) < 0
  have hi := e.property.2 i.down
  omega

def negativeToPositiveMonomialExponent (k : ℕ) (e : fullNegativeMonomialExponent ι k) :
    positiveMonomialExponent ι k := by
  let v : ι →₀ ℕ := Finsupp.mapRange (fun z : ℤ => (-z).toNat) (by simp) e.val.val
  have hcast (i : ι) : (v i : ℤ) = -e.val.val i :=
    Int.toNat_of_nonneg (neg_nonneg.mpr (fullNegativeMonomialExponent_lt k e i).le)
  have he : (∑ i : ι, e.val.val i) = -(k : ℤ) :=
    (Finsupp.degree_eq_sum e.val.val).symm.trans e.val.property
  have hv : v.degree = k := by
    apply Int.ofNat_inj.mp
    rw [Finsupp.degree_eq_sum, Nat.cast_sum]
    calc
      (∑ i : ι, (v i : ℤ)) = ∑ i : ι, -e.val.val i := Finset.sum_congr rfl (fun i _ => hcast i)
      _ = k := by rw [Finset.sum_neg_distrib, he, neg_neg]
  refine ⟨v, hv, ?_⟩
  intro i
  have hi := fullNegativeMonomialExponent_lt k e i
  have hc := hcast i
  omega

def negativeLaurentMonomialExponentEquiv (k : ℕ) :
    positiveMonomialExponent ι k ≃ fullNegativeMonomialExponent ι k where
  toFun := positiveToNegativeMonomialExponent k
  invFun := negativeToPositiveMonomialExponent k
  left_inv e := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    change (-(-(e.val i : ℤ))).toNat = e.val i
    rw [neg_neg, Int.toNat_natCast]
  right_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    change -(((-e.val.val i).toNat : ℕ) : ℤ) = e.val.val i
    rw [Int.toNat_of_nonneg (neg_nonneg.mpr (fullNegativeMonomialExponent_lt k e i).le), neg_neg]

end

end OAI.AlgebraicGeometry.Comparison.Betti.NegativeLaurentMonomialExponents.Dolbeault
