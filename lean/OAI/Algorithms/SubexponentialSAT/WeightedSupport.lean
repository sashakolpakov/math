import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-!
# The weighted support bound for the symbolic incidence polynomials

The outer polynomial variable is U, the middle polynomial variable is Z,
and the innermost multivariate polynomial has the formal input coordinates.
An admissible polynomial only has monomials with degX ≤ degU + degZ.
-/

namespace SubexponentialSAT.WeightedSupport

noncomputable section

open scoped BigOperators

variable {ι R : Type*} [CommSemiring R]

abbrev Poly (ι R : Type*) [CommSemiring R] :=
  Polynomial (Polynomial (MvPolynomial ι R))

/-- The coefficient form of the weighted monomial support condition. -/
def Admissible (P : Poly ι R) : Prop :=
  ∀ j r, ((P.coeff j).coeff r).totalDegree ≤ j + r

theorem admissible_iff_support (P : Poly ι R) :
    Admissible P ↔
      ∀ j r a, a ∈ ((P.coeff j).coeff r).support →
        a.sum (fun _ n => n) ≤ j + r := by
  constructor
  · intro h j r a ha
    exact (MvPolynomial.le_totalDegree ha).trans (h j r)
  · intro h j r
    exact Finset.sup_le (fun a ha => h j r a ha)

@[simp] theorem admissible_zero : Admissible (0 : Poly ι R) := by
  intro j r
  simp

theorem admissible_add {P Q : Poly ι R}
    (hP : Admissible P) (hQ : Admissible Q) : Admissible (P + Q) := by
  intro j r
  simp only [Polynomial.coeff_add]
  exact (MvPolynomial.totalDegree_add _ _).trans (max_le (hP j r) (hQ j r))

theorem admissible_mul {P Q : Poly ι R}
    (hP : Admissible P) (hQ : Admissible Q) : Admissible (P * Q) := by
  classical
  intro j r
  rw [Polynomial.coeff_mul, Polynomial.finsetSum_coeff]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro uv huv
  rw [Polynomial.coeff_mul]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro st hst
  have huv' : uv.1 + uv.2 = j := Finset.HasAntidiagonal.mem_antidiagonal.mp huv
  have hst' : st.1 + st.2 = r := Finset.HasAntidiagonal.mem_antidiagonal.mp hst
  apply (MvPolynomial.totalDegree_mul _ _).trans
  have hp := hP uv.1 st.1
  have hq := hQ uv.2 st.2
  omega

/-- A single U/Z monomial is admissible whenever its X coefficient fits. -/
theorem admissible_monomial (j r : ℕ) (f : MvPolynomial ι R)
    (hf : f.totalDegree ≤ j + r) :
    Admissible (Polynomial.monomial j (Polynomial.monomial r f)) := by
  intro k s
  by_cases hj : j = k
  · subst k
    by_cases hr : r = s
    · subst s
      simpa using hf
    · simp [Polynomial.coeff_monomial, hr]
  · simp [Polynomial.coeff_monomial, hj]

/-- Embed a scalar as a polynomial constant in all three groups of variables. -/
def scalarHom : R →+* Poly ι R :=
  Polynomial.C.comp (Polynomial.C.comp MvPolynomial.C)

@[simp] theorem scalarHom_apply (c : R) :
    scalarHom (ι := ι) c = Polynomial.C (Polynomial.C (MvPolynomial.C c)) := rfl

theorem admissible_scalar (c : R) : Admissible (scalarHom (ι := ι) c) := by
  simpa [scalarHom] using
    admissible_monomial (ι := ι) 0 0 (MvPolynomial.C c) (by simp)

@[simp] theorem admissible_one : Admissible (1 : Poly ι R) := by
  simpa using admissible_scalar (ι := ι) (1 : R)

theorem admissible_pow {P : Poly ι R} (hP : Admissible P) (n : ℕ) :
    Admissible (P ^ n) := by
  induction n with
  | zero => exact admissible_one (ι := ι) (R := R)
  | succ n ih =>
    rw [pow_succ]
    exact admissible_mul ih hP

theorem admissible_sum {α : Type*} (s : Finset α) (f : α → Poly ι R)
    (hf : ∀ a ∈ s, Admissible (f a)) : Admissible (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact admissible_add (hf a (Finset.mem_insert_self a s))
      (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

theorem admissible_prod {α : Type*} (s : Finset α) (f : α → Poly ι R)
    (hf : ∀ a ∈ s, Admissible (f a)) : Admissible (∏ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact admissible_one (ι := ι) (R := R)
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact admissible_mul (hf a (Finset.mem_insert_self a s))
      (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

/-- Substituting admissible incidence arguments into any table polynomial
preserves the weighted support condition. -/
theorem admissible_eval₂ {σ : Type*} (F : MvPolynomial σ R)
    (C : σ → Poly ι R) (hC : ∀ i, Admissible (C i)) :
    Admissible (MvPolynomial.eval₂ (scalarHom (ι := ι)) C F) := by
  induction F using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.eval₂_C]
    exact admissible_scalar c
  | add p q hp hq =>
    simpa only [MvPolynomial.eval₂_add] using admissible_add hp hq
  | mul_X p i hp =>
    simpa only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] using
      admissible_mul hp (hC i)

/-- An actual finite linear form in the formal input coordinates. -/
def linearForm (s : Finset ι) (a : ι → R) : MvPolynomial ι R :=
  ∑ i ∈ s, MvPolynomial.monomial (Finsupp.single i 1) (a i)

theorem linearForm_degree (s : Finset ι) (a : ι → R) :
    (linearForm s a).totalDegree ≤ 1 := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  simpa using MvPolynomial.totalDegree_monomial_le (Finsupp.single i 1) (a i)

theorem linear_add_constant_degree (L : MvPolynomial ι R)
    (hL : L.totalDegree ≤ 1) (c : R) :
    (L + MvPolynomial.C c).totalDegree ≤ 1 :=
  (MvPolynomial.totalDegree_add _ _).trans (max_le hL (by simp))

/-- The symbolic form beta + U defect + positive-Z linear terms. -/
def markedArgument (β : R) (defect : MvPolynomial ι R)
    (s : Finset ℕ) (rows : ℕ → MvPolynomial ι R) : Poly ι R :=
  scalarHom β +
    Polynomial.monomial 1 (Polynomial.monomial 0 defect) +
    ∑ r ∈ s, Polynomial.monomial 0 (Polynomial.monomial r (rows r))

theorem admissible_markedArgument (β : R) (defect : MvPolynomial ι R)
    (s : Finset ℕ) (rows : ℕ → MvPolynomial ι R)
    (hdefect : defect.totalDegree ≤ 1)
    (hpos : ∀ r ∈ s, 0 < r)
    (hrows : ∀ r ∈ s, (rows r).totalDegree ≤ 1) :
    Admissible (markedArgument β defect s rows) := by
  apply admissible_add
  · exact admissible_add (admissible_scalar β)
      (admissible_monomial 1 0 defect (by simpa using hdefect))
  · apply admissible_sum
    intro r hr
    apply admissible_monomial
    have hp := hpos r hr
    have hd := hrows r hr
    omega

/-- Products of arbitrary table polynomials evaluated at admissible arguments. -/
theorem admissible_factor_product {α : Type*} {σ : α → Type*}
    (s : Finset α) (F : ∀ e, MvPolynomial (σ e) R)
    (C : ∀ e, σ e → Poly ι R)
    (hC : ∀ e ∈ s, ∀ i, Admissible (C e i)) :
    Admissible (∏ e ∈ s, MvPolynomial.eval₂ (scalarHom (ι := ι)) (C e) (F e)) := by
  apply admissible_prod
  intro e he
  exact admissible_eval₂ (F e) (C e) (hC e he)

/-- The surviving U/Z rectangle has strictly smaller X degree than D + μ. -/
theorem retained_degree_bound {P : Poly ι R} (hP : Admissible P)
    {μ D j r : ℕ} (hj : j < μ) (hr : r < D) :
    ((P.coeff j).coeff r).totalDegree ≤ μ + D - 2 := by
  exact (hP j r).trans (by omega)

theorem retained_support_bound {P : Poly ι R} (hP : Admissible P)
    {μ D j r : ℕ} (hj : j < μ) (hr : r < D)
    {a : ι →₀ ℕ} (ha : a ∈ ((P.coeff j).coeff r).support) :
    a.sum (fun _ n => n) ≤ μ + D - 2 := by
  exact (MvPolynomial.le_totalDegree ha).trans (retained_degree_bound hP hj hr)

theorem retained_degree_lt {P : Poly ι R} (hP : Admissible P)
    {μ D j r : ℕ} (hj : j < μ) (hr : r < D) :
    ((P.coeff j).coeff r).totalDegree < μ + D := by
  have h := hP j r
  omega

/-- Retain only input-coordinate monomials of total degree at most N. -/
def xTrunc (N : ℕ) (P : MvPolynomial ι R) : MvPolynomial ι R :=
  AddMonoidAlgebra.ofCoeff
    (Finsupp.filter (fun a : ι →₀ ℕ => a.sum (fun _ k => k) ≤ N)
      (AddMonoidAlgebra.coeff P))

@[simp] theorem coeff_xTrunc (N : ℕ) (a : ι →₀ ℕ) (P : MvPolynomial ι R) :
    (xTrunc N P).coeff a =
      if a.sum (fun _ k => k) ≤ N then P.coeff a else 0 := by
  classical
  simp [xTrunc, Finsupp.filter_apply]

@[simp] theorem xTrunc_zero (N : ℕ) : xTrunc N (0 : MvPolynomial ι R) = 0 := by
  ext a
  simp

theorem xTrunc_add (N : ℕ) (P Q : MvPolynomial ι R) :
    xTrunc N (P + Q) = xTrunc N P + xTrunc N Q := by
  ext a
  by_cases h : a.sum (fun _ k => k) ≤ N <;> simp [h]

theorem xTrunc_eq_self_of_degree_le (N : ℕ) (P : MvPolynomial ι R)
    (hP : P.totalDegree ≤ N) : xTrunc N P = P := by
  classical
  ext a
  by_cases ha : a.sum (fun _ k => k) ≤ N
  · simp [ha]
  · have hz : P.coeff a = 0 := by
      by_contra hn
      exact ha ((MvPolynomial.le_totalDegree
        (MvPolynomial.mem_support_iff.mpr hn)).trans hP)
    simp [ha, hz]

theorem retained_xTrunc_eq_self {P : Poly ι R} (hP : Admissible P)
    {μ D j r : ℕ} (hj : j < μ) (hr : r < D) :
    xTrunc (D + μ) ((P.coeff j).coeff r) = (P.coeff j).coeff r := by
  apply xTrunc_eq_self_of_degree_le
  have h := retained_degree_lt hP hj hr
  omega

/-- Total X degree is monotone under multiplication, so early clipping is safe. -/
theorem xTrunc_mul (N : ℕ) (P Q : MvPolynomial ι R) :
    xTrunc N (xTrunc N P * xTrunc N Q) = xTrunc N (P * Q) := by
  classical
  ext a
  simp only [coeff_xTrunc]
  by_cases ha : a.sum (fun _ k => k) ≤ N
  · simp only [ite_eq_left ha, MvPolynomial.coeff_mul]
    apply Finset.sum_congr rfl
    intro b hb
    have hab : b.1 + b.2 = a := Finset.HasAntidiagonal.mem_antidiagonal.mp hb
    have hsum : b.1.sum (fun _ k => k) + b.2.sum (fun _ k => k) =
        a.sum (fun _ k => k) := by
      rw [← hab, Finsupp.sum_add_index']
      · intro i
        rfl
      · intro i x y
        rfl
    have h1 : b.1.sum (fun _ k => k) ≤ N := by omega
    have h2 : b.2.sum (fun _ k => k) ≤ N := by omega
    simp [h1, h2]
  · simp [ha]

section Ring

variable {S : Type*} [CommRing S]

/-- The exact incidence-argument shape: beta + U (L - beta) + Z-tail. -/
def incidenceArgument (β : S) (L : MvPolynomial ι S)
    (s : Finset ℕ) (rows : ℕ → MvPolynomial ι S) : Poly ι S :=
  markedArgument β (L - (MvPolynomial.C β : MvPolynomial ι S)) s rows

theorem admissible_incidenceArgument (β : S) (L : MvPolynomial ι S)
    (s : Finset ℕ) (rows : ℕ → MvPolynomial ι S)
    (hL : L.totalDegree ≤ 1)
    (hpos : ∀ r ∈ s, 0 < r)
    (hrows : ∀ r ∈ s, (rows r).totalDegree ≤ 1) :
    Admissible (incidenceArgument β L s rows) := by
  apply admissible_markedArgument β (L - (MvPolynomial.C β : MvPolynomial ι S)) s rows
  · simpa [sub_eq_add_neg] using linear_add_constant_degree L hL (-β)
  · exact hpos
  · exact hrows

/-- Actual finite linear forms discharge all the X-degree assumptions. -/
theorem admissible_incidence_linearForms (β : S) (coordinates : Finset ι)
    (a : ι → S) (s : Finset ℕ) (b : ℕ → ι → S)
    (hpos : ∀ r ∈ s, 0 < r) :
    Admissible (incidenceArgument β (linearForm coordinates a) s
      (fun r => linearForm coordinates (b r))) := by
  apply admissible_incidenceArgument
  · exact linearForm_degree coordinates a
  · exact hpos
  · intro r hr
    exact linearForm_degree coordinates (b r)

end Ring

end

end SubexponentialSAT.WeightedSupport

end OAI.Algorithms
