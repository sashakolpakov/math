import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-!
# Counting the retained symbolic monomials

The exponent vectors are genuine natural-valued functions (and, equivalently,
finitely supported functions) with a bound on the sum of their entries.  Adding
a slack coordinate identifies them with weak compositions, so that stars and
bars counts the actual exponent vectors.
-/

namespace SubexponentialSAT.MonomialCount

open scoped BigOperators

/-- Exponent vectors in `D` variables of total degree at most `N`. -/
def BoundedExponents (D N : ℕ) :=
  {a : Fin D → ℕ // ∑ i, a i ≤ N}

/-- Adding the unused degree as the first coordinate makes a weak composition. -/
def slackEquiv (D N : ℕ) :
    BoundedExponents D N ≃ {a : Fin (D + 1) → ℕ // ∑ i, a i = N} where
  toFun a := ⟨Fin.cons (N - ∑ i, a.1 i) a.1, by
    simpa only [Fin.sum_cons] using Nat.sub_add_cancel a.2⟩
  invFun a := ⟨fun i => a.1 i.succ, by
    have h := a.2
    rw [Fin.sum_univ_succ] at h
    exact (Nat.le_add_left (∑ i : Fin D, a.1 i.succ) (a.1 0)).trans_eq h⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    rfl
  right_inv a := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => rfl) i
    simp only [Fin.cons_zero]
    have h := a.2
    rw [Fin.sum_univ_succ] at h
    omega

/-- The stars-and-bars equivalence for degree-bounded exponent vectors. -/
noncomputable def boundedEquivSym (D N : ℕ) :
    BoundedExponents D N ≃ Sym (Fin (D + 1)) N :=
  (slackEquiv D N).trans (Sym.equivNatSumOfFintype (Fin (D + 1)) N).symm

noncomputable instance boundedExponentsFintype (D N : ℕ) :
    Fintype (BoundedExponents D N) :=
  Fintype.ofEquiv (Sym (Fin (D + 1)) N) (boundedEquivSym D N).symm

/-- Exact cardinality of the actual degree-bounded exponent vectors. -/
theorem card_boundedExponents (D N : ℕ) :
    Fintype.card (BoundedExponents D N) = (D + N).choose D := by
  rw [Fintype.card_congr (boundedEquivSym D N), Sym.card_sym_eq_choose]
  simp only [Fintype.card_fin]
  have h : D + 1 + N - 1 = D + N := by omega
  rw [h]
  exact Nat.choose_symm_add.symm

/-- The equivalent exponent-vector type used by multivariate polynomials. -/
def BoundedFinsupp (D N : ℕ) :=
  {a : Fin D →₀ ℕ // a.sum (fun _ n => n) ≤ N}

noncomputable def boundedFinsuppEquiv (D N : ℕ) :
    BoundedFinsupp D N ≃ BoundedExponents D N :=
  Finsupp.equivFunOnFinite.subtypeEquiv (by
    intro a
    simp [Finsupp.sum_fintype])

noncomputable instance boundedFinsuppFintype (D N : ℕ) :
    Fintype (BoundedFinsupp D N) :=
  Fintype.ofEquiv (BoundedExponents D N) (boundedFinsuppEquiv D N).symm

theorem card_boundedFinsupp (D N : ℕ) :
    Fintype.card (BoundedFinsupp D N) = (D + N).choose D := by
  rw [Fintype.card_congr (boundedFinsuppEquiv D N), card_boundedExponents]

/-- The retained `X` monomials for `μ = D + 1`. -/
abbrev RetainedX (D : ℕ) := BoundedFinsupp D (2 * D + 1)

theorem card_retainedX (D : ℕ) :
    Fintype.card (RetainedX D) = (3 * D + 1).choose D := by
  rw [card_boundedFinsupp]
  congr 1
  omega

theorem card_retainedX_le (D : ℕ) :
    Fintype.card (RetainedX D) ≤ 2 ^ (3 * D + 1) := by
  rw [card_retainedX]
  exact Nat.choose_le_two_pow (3 * D + 1) D

/-- The fifth power includes four symbolic-operation factors and one moment loop.
This is an arithmetic bound on the index count, not a machine-runtime theorem. -/
theorem card_retainedX_pow_five_le (D : ℕ) :
    Fintype.card (RetainedX D) ^ 5 ≤ 2 ^ (15 * D + 5) := by
  calc
    Fintype.card (RetainedX D) ^ 5 ≤ (2 ^ (3 * D + 1)) ^ 5 :=
      Nat.pow_le_pow_left (card_retainedX_le D) 5
    _ = 2 ^ ((3 * D + 1) * 5) := (pow_mul _ _ _).symm
    _ = 2 ^ (15 * D + 5) := by congr 1; omega

theorem card_retainedX_pow_five_le_budget (D : ℕ) (hD : 1 ≤ D) :
    Fintype.card (RetainedX D) ^ 5 ≤ 2 ^ (128 * D) := by
  apply (card_retainedX_pow_five_le D).trans
  exact Nat.pow_le_pow_right (by decide) (by omega)

/-- Independent retained exponents of `U` and `Z`. -/
abbrev UZIndices (μ D : ℕ) := Fin μ × Fin D

theorem card_uzIndices (μ D : ℕ) :
    Fintype.card (UZIndices μ D) = μ * D := by
  simp [UZIndices]

/-- A coefficient slot in the full canonical symbolic representative. -/
abbrev RetainedMonomial (D : ℕ) := RetainedX D × UZIndices (D + 1) D

theorem card_retainedMonomial (D : ℕ) :
    Fintype.card (RetainedMonomial D) =
      (3 * D + 1).choose D * ((D + 1) * D) := by
  simp only [RetainedMonomial, Fintype.card_prod, card_retainedX, Fintype.card_fin]

theorem card_retainedMonomial_le (D : ℕ) :
    Fintype.card (RetainedMonomial D) ≤
      2 ^ (3 * D + 1) * ((D + 1) * D) := by
  rw [card_retainedMonomial]
  exact Nat.mul_le_mul_right _ (Nat.choose_le_two_pow (3 * D + 1) D)

end SubexponentialSAT.MonomialCount

end OAI.Algorithms
