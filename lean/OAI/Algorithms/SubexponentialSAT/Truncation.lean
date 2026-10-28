import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.WeightedSupport
import OAI.Algorithms.SubexponentialSAT.NilpotentDefect

namespace OAI.Algorithms

/-!
# Canonical truncation before substitution

Polynomials are represented with U outermost, Z in the middle, and the X variables
innermost.  Truncation is an operation on canonical polynomial representatives;
we never assert that U = 1 defines a map out of the truncated quotient.
-/

namespace SubexponentialSAT.Truncation

noncomputable section

open scoped BigOperators

variable {R ι : Type*} [CommSemiring R]

abbrev Poly (ι R : Type*) [CommSemiring R] :=
  Polynomial (Polynomial (MvPolynomial ι R))

/-- Delete all coefficients of degree at least n. -/
def trunc {A : Type*} [Semiring A] (n : ℕ) (P : Polynomial A) : Polynomial A :=
  Polynomial.ofFinsupp (.ofCoeff (P.toFinsupp.coeff.filter fun j => j < n))

@[simp] theorem coeff_trunc {A : Type*} [Semiring A]
    (n j : ℕ) (P : Polynomial A) :
    (trunc n P).coeff j = if j < n then P.coeff j else 0 := by
  classical
  simp [trunc, Polynomial.coeff, Finsupp.filter_apply]

@[simp] theorem trunc_zero {A : Type*} [Semiring A] (n : ℕ) :
    trunc n (0 : Polynomial A) = 0 := by
  ext j
  simp

@[simp] theorem trunc_add {A : Type*} [Semiring A]
    (n : ℕ) (P Q : Polynomial A) :
    trunc n (P + Q) = trunc n P + trunc n Q := by
  ext j
  by_cases h : j < n <;> simp [h]

/-- Delete X monomials whose total degree exceeds N. -/
def xTrunc (N : ℕ) (P : MvPolynomial ι R) : MvPolynomial ι R :=
  .ofCoeff ((AddMonoidAlgebra.coeff P).filter
    fun a : ι →₀ ℕ => a.sum (fun _ k => k) ≤ N)

@[simp] theorem coeff_xTrunc (N : ℕ) (a : ι →₀ ℕ) (P : MvPolynomial ι R) :
    (xTrunc N P).coeff a =
      if a.sum (fun _ k => k) ≤ N then P.coeff a else 0 := by
  classical
  simp [xTrunc, Finsupp.filter_apply]

@[simp] theorem xTrunc_zero (N : ℕ) : xTrunc N (0 : MvPolynomial ι R) = 0 := by
  ext a
  simp

@[simp] theorem xTrunc_add (N : ℕ) (P Q : MvPolynomial ι R) :
    xTrunc N (P + Q) = xTrunc N P + xTrunc N Q := by
  ext a
  by_cases h : a.sum (fun _ k => k) ≤ N <;> simp [h]

def xTruncAddHom (N : ℕ) : MvPolynomial ι R →+ MvPolynomial ι R where
  toFun := xTrunc N
  map_zero' := xTrunc_zero N
  map_add' := xTrunc_add N

theorem xTrunc_eq_self (N : ℕ) (P : MvPolynomial ι R)
    (h : P.totalDegree ≤ N) : xTrunc N P = P := by
  classical
  ext a
  by_cases ha : a.sum (fun _ k => k) ≤ N
  · simp [ha]
  · have hz : P.coeff a = 0 :=
      MvPolynomial.coeff_eq_zero_of_totalDegree_lt (by
        exact lt_of_le_of_lt h (Nat.lt_of_not_ge ha))
    simp [ha, hz]

/-- Retain precisely U^j Z^r X^a with j < μ, r < D, and |a| ≤ N. -/
def canonical (μ D N : ℕ) (P : Poly ι R) : Poly ι R :=
  ∑ j ∈ Finset.range μ, Polynomial.monomial j
    (∑ r ∈ Finset.range D, Polynomial.monomial r (xTrunc N ((P.coeff j).coeff r)))

@[simp] theorem coeff_canonical (μ D N j r : ℕ) (P : Poly ι R) :
    ((canonical μ D N P).coeff j).coeff r =
      if j < μ ∧ r < D then xTrunc N ((P.coeff j).coeff r) else 0 := by
  classical
  by_cases hj : j < μ <;>
    simp [canonical, Polynomial.coeff_monomial, hj]

/-- Evaluate only the X coordinates, leaving both U and Z formal. -/
def substX (x : ι → R) : Poly ι R →+* Polynomial (Polynomial R) :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (MvPolynomial.eval x))

@[simp] theorem coeff_substX (x : ι → R) (P : Poly ι R) (j r : ℕ) :
    (((substX x) P).coeff j).coeff r =
      MvPolynomial.eval x ((P.coeff j).coeff r) := by
  simp [substX]

/-- Apply an additive map to every polynomial coefficient. -/
def mapCoeffs {A B : Type*} [Semiring A] [Semiring B]
    (f : A →+ B) : Polynomial A →+ Polynomial B where
  toFun P := Polynomial.ofFinsupp (.ofCoeff (P.toFinsupp.coeff.mapRange f f.map_zero))
  map_zero' := by ext j; simp [Polynomial.coeff]
  map_add' P Q := by
    ext j
    rw [Polynomial.coeff_add]
    change f ((P + Q).coeff j) = f (P.coeff j) + f (Q.coeff j)
    rw [Polynomial.coeff_add, map_add]

@[simp] theorem coeff_mapCoeffs {A B : Type*} [Semiring A] [Semiring B]
    (f : A →+ B) (P : Polynomial A) (j : ℕ) :
    (mapCoeffs f P).coeff j = f (P.coeff j) := by
  rfl

@[simp] theorem mapCoeffs_monomial {A B : Type*} [Semiring A] [Semiring B]
    (f : A →+ B) (j : ℕ) (a : A) :
    mapCoeffs f (Polynomial.monomial j a) = Polynomial.monomial j (f a) := by
  ext r
  simp only [coeff_mapCoeffs, Polynomial.coeff_monomial]
  split_ifs <;> simp_all

theorem eval_one_mapCoeffs {A B : Type*} [Semiring A] [Semiring B]
    (f : A →+ B) (P : Polynomial A) :
    (mapCoeffs f P).eval 1 = f (P.eval 1) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, Polynomial.eval_add, hP, hQ]
  | monomial j a => simp

def truncAddHom {A : Type*} [Semiring A] (n : ℕ) :
    Polynomial A →+ Polynomial A where
  toFun := trunc n
  map_zero' := trunc_zero n
  map_add' := trunc_add n

/-- Lift a coefficient reduction and a monomial cutoff together. -/
def clipAddHom {A : Type*} [Semiring A] (n : ℕ) (f : A →+ A) :
    Polynomial A →+ Polynomial A :=
  (mapCoeffs f).comp (truncAddHom n)

@[simp] theorem coeff_clipAddHom {A : Type*} [Semiring A]
    (n : ℕ) (f : A →+ A) (P : Polynomial A) (j : ℕ) :
    (clipAddHom n f P).coeff j = if j < n then f (P.coeff j) else 0 := by
  change f ((trunc n P).coeff j) = _
  rw [coeff_trunc]
  split_ifs <;> simp

/-- A stable coefficient reduction stays stable after adjoining a variable
and deleting high powers of that variable. -/
theorem clipAddHom_mul {A : Type*} [Semiring A] (n : ℕ) (f : A →+ A)
    (hf : ∀ a b, f (f a * f b) = f (a * b)) (P Q : Polynomial A) :
    clipAddHom n f (clipAddHom n f P * clipAddHom n f Q) =
      clipAddHom n f (P * Q) := by
  classical
  ext j
  by_cases hj : j < n
  · simp only [coeff_clipAddHom, ite_eq_left hj, Polynomial.coeff_mul, map_sum]
    apply Finset.sum_congr rfl
    intro ab hab
    have hab' : ab.1 + ab.2 = j := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have ha : ab.1 < n := by omega
    have hb : ab.2 < n := by omega
    simp only [ ite_eq_left ha, ite_eq_left hb]
    exact hf _ _
  · simp [hj]

theorem canonical_eq_clip (μ D N : ℕ) (P : Poly ι R) :
    canonical μ D N P =
      clipAddHom μ (clipAddHom D (xTruncAddHom N)) P := by
  ext j r
  by_cases hj : j < μ <;> by_cases hr : r < D <;>
    simp [coeff_canonical, coeff_clipAddHom, hj, hr, xTruncAddHom]

@[simp] theorem canonical_add (μ D N : ℕ) (P Q : Poly ι R) :
    canonical μ D N (P + Q) = canonical μ D N P + canonical μ D N Q := by
  simp only [canonical_eq_clip, map_add]

@[simp] theorem canonical_zero (μ D N : ℕ) :
    canonical μ D N (0 : Poly ι R) = 0 := by
  simp only [canonical_eq_clip, map_zero]

theorem canonical_sum {α : Type*} (μ D N : ℕ) (s : Finset α)
    (P : α → Poly ι R) :
    canonical μ D N (∑ a ∈ s, P a) = ∑ a ∈ s, canonical μ D N (P a) := by
  simp only [canonical_eq_clip, map_sum]

theorem xTrunc_C_mul (N : ℕ) (c : R) (P : MvPolynomial ι R) :
    xTrunc N (MvPolynomial.C c * P) = MvPolynomial.C c * xTrunc N P := by
  ext a
  by_cases ha : a.sum (fun _ k => k) ≤ N <;>
    simp [coeff_xTrunc, MvPolynomial.coeff_C_mul, ha]

theorem canonical_scalar_mul (μ D N : ℕ) (c : R) (P : Poly ι R) :
    canonical μ D N (SubexponentialSAT.WeightedSupport.scalarHom (ι := ι) c * P) =
      SubexponentialSAT.WeightedSupport.scalarHom (ι := ι) c * canonical μ D N P := by
  ext j r
  by_cases h : j < μ ∧ r < D <;>
    simp [coeff_canonical, SubexponentialSAT.WeightedSupport.scalarHom,
      Polynomial.coeff_C_mul, xTrunc_C_mul, h]

/-- Multiplying canonical representatives and reducing again gives the same
representative as reducing the full product. This is the quotient-product
bridge needed when the two factor groups were truncated separately. -/
theorem canonical_mul (μ D N : ℕ) (P Q : Poly ι R) :
    canonical μ D N (canonical μ D N P * canonical μ D N Q) =
      canonical μ D N (P * Q) := by
  simp only [canonical_eq_clip]
  apply clipAddHom_mul
  intro A B
  apply clipAddHom_mul
  intro a b
  exact SubexponentialSAT.WeightedSupport.xTrunc_mul N a b

/-- Truncate Z, separately in each complete U coefficient. -/
def truncZ {A : Type*} [Semiring A] (D : ℕ)
    (P : Polynomial (Polynomial A)) : Polynomial (Polynomial A) :=
  mapCoeffs (truncAddHom D) P

@[simp] theorem coeff_truncZ {A : Type*} [Semiring A]
    (D j r : ℕ) (P : Polynomial (Polynomial A)) :
    ((truncZ D P).coeff j).coeff r =
      if r < D then (P.coeff j).coeff r else 0 := by
  exact coeff_trunc D r (P.coeff j)

/-- The X cutoff is harmless in all retained U,Z coefficients, while the
discarded complete U coefficients vanish after substitution. -/
theorem substX_canonical (x : ι → R) (μ D N : ℕ) (P : Poly ι R)
    (hN : D + μ ≤ N)
    (hdeg : ∀ j r, ((P.coeff j).coeff r).totalDegree ≤ j + r)
    (hhigh : ∀ j, μ ≤ j → ((substX x) P).coeff j = 0) :
    (substX x) (canonical μ D N P) = truncZ D ((substX x) P) := by
  ext j r
  by_cases hj : j < μ
  · by_cases hr : r < D
    · have hd : ((P.coeff j).coeff r).totalDegree ≤ N :=
        (hdeg j r).trans (by omega)
      simp [coeff_substX, coeff_canonical, hj, hr, xTrunc_eq_self N _ hd]
    · simp [coeff_substX, coeff_canonical, hj, hr]
  · have hz := hhigh j (Nat.le_of_not_gt hj)
    rw [coeff_substX, coeff_canonical]
    simp only [hj, false_and, ↓reduceIte, map_zero]
    rw [coeff_truncZ, hz]
    simp

/-- Lemma 4.2's central truncation/substitution identity. Its hypotheses are
the independently established support-degree invariant and nilpotence of
high U coefficients after X substitution, not the desired equality itself. -/
theorem canonical_substitution (x : ι → R) (μ D N : ℕ) (P : Poly ι R)
    (hN : D + μ ≤ N)
    (hdeg : ∀ j r, ((P.coeff j).coeff r).totalDegree ≤ j + r)
    (hhigh : ∀ j, μ ≤ j → ((substX x) P).coeff j = 0) :
    ((substX x) (canonical μ D N P)).eval 1 =
      trunc D (((substX x) P).eval 1) := by
  rw [substX_canonical x μ D N P hN hdeg hhigh]
  exact eval_one_mapCoeffs (truncAddHom D) ((substX x) P)

/-- Divisibility by powers of a nilpotent coefficient implies the high-U
vanishing required by the preceding theorem. In the application q is C(p). -/
theorem canonical_substitution_of_divisible (x : ι → R) (μ D N : ℕ)
    (P : Poly ι R) (q : Polynomial R)
    (hN : D + μ ≤ N)
    (hdeg : ∀ j r, ((P.coeff j).coeff r).totalDegree ≤ j + r)
    (hnil : q ^ μ = 0)
    (hdiv : ∀ j, q ^ j ∣ ((substX x) P).coeff j) :
    ((substX x) (canonical μ D N P)).eval 1 =
      trunc D (((substX x) P).eval 1) := by
  apply canonical_substitution x μ D N P hN hdeg
  intro j hj
  apply eq_zero_of_zero_dvd
  simpa only [pow_eq_zero_of_le hj hnil] using hdiv j

theorem canonical_substitution_coeff (x : ι → R) (μ D N : ℕ)
    (P : Poly ι R)
    (hN : D + μ ≤ N)
    (hdeg : ∀ j r, ((P.coeff j).coeff r).totalDegree ≤ j + r)
    (hhigh : ∀ j, μ ≤ j → ((substX x) P).coeff j = 0)
    (r : ℕ) (hr : r < D) :
    (((substX x) (canonical μ D N P)).eval 1).coeff r =
      (((substX x) P).eval 1).coeff r := by
  rw [canonical_substitution x μ D N P hN hdeg hhigh, coeff_trunc, ite_eq_left hr]

/-- The exact order of operations in Lemma 4.2, including independently
truncated groups and their product in the truncated polynomial ring. -/
theorem truncated_groups_substitution (x : ι → R) (μ D : ℕ)
    (P Q : Poly ι R)
    (hP : SubexponentialSAT.WeightedSupport.Admissible P)
    (hQ : SubexponentialSAT.WeightedSupport.Admissible Q)
    (hhigh : ∀ j, μ ≤ j → ((substX x) (P * Q)).coeff j = 0) :
    ((substX x)
      (canonical μ D (D + μ)
        (canonical μ D (D + μ) P * canonical μ D (D + μ) Q))).eval 1 =
      trunc D (((substX x) (P * Q)).eval 1) := by
  rw [canonical_mul]
  apply canonical_substitution x μ D (D + μ) (P * Q) le_rfl
  · exact SubexponentialSAT.WeightedSupport.admissible_mul hP hQ
  · exact hhigh

/-- Ordinary evaluation on the full polynomial, first in X and then at U=1. -/
def evalXU (x : ι → R) : Poly ι R →+* Polynomial R :=
  (Polynomial.evalRingHom 1).comp (substX x)

@[simp] theorem evalXU_apply (x : ι → R) (P : Poly ι R) :
    evalXU x P = ((substX x) P).eval 1 := rfl

theorem evalXU_factor {σ : Type*} (x : ι → R)
    (F : MvPolynomial σ R) (C : σ → Poly ι R) :
    evalXU x (MvPolynomial.eval₂ (SubexponentialSAT.WeightedSupport.scalarHom (ι := ι)) C F) =
      MvPolynomial.eval₂ Polynomial.C (fun i => evalXU x (C i)) F := by
  have hs : (evalXU x).comp (SubexponentialSAT.WeightedSupport.scalarHom (ι := ι)) =
      Polynomial.C := by
    ext c
    simp [evalXU, substX, SubexponentialSAT.WeightedSupport.scalarHom]
  have h := MvPolynomial.eval₂_comp_left (evalXU x)
    (SubexponentialSAT.WeightedSupport.scalarHom (ι := ι)) C F
  rw [hs] at h
  exact h

theorem evalXU_factor_product {α : Type*} {σ : α → Type*}
    (x : ι → R) (s : Finset α) (F : ∀ e, MvPolynomial (σ e) R)
    (C : ∀ e, σ e → Poly ι R) :
    evalXU x (∏ e ∈ s,
      MvPolynomial.eval₂ (SubexponentialSAT.WeightedSupport.scalarHom (ι := ι)) (C e) (F e)) =
      ∏ e ∈ s, MvPolynomial.eval₂ Polynomial.C (fun i => evalXU x (C e i)) (F e) := by
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro e he
  exact evalXU_factor x (F e) (C e)

section Ring

variable {S : Type*} [CommRing S]

/-- Substitution cancels the arbitrary residue lift beta and restores the
original row's constant value together with all positive-Z coefficients. -/
theorem evalXU_incidenceArgument (x : ι → S) (β : S)
    (L : MvPolynomial ι S) (s : Finset ℕ) (rows : ℕ → MvPolynomial ι S) :
    evalXU x (SubexponentialSAT.WeightedSupport.incidenceArgument β L s rows) =
      Polynomial.C (MvPolynomial.eval x L) +
        ∑ r ∈ s, Polynomial.monomial r (MvPolynomial.eval x (rows r)) := by
  classical
  simp [evalXU, substX, SubexponentialSAT.WeightedSupport.incidenceArgument,
    SubexponentialSAT.WeightedSupport.markedArgument, SubexponentialSAT.WeightedSupport.scalarHom,
    Polynomial.eval_finsetSum ]

/-- A finite group of factors evaluated at the actual marked incidence
arguments of equation (4.3). -/
def incidenceProduct {α : Type*} {σ : α → Type*} (s : Finset α)
    (F : ∀ e, MvPolynomial (σ e) S)
    (β : ∀ e, σ e → S) (L : ∀ e, σ e → MvPolynomial ι S)
    (zs : ∀ e, σ e → Finset ℕ)
    (rows : ∀ e, σ e → ℕ → MvPolynomial ι S) : Poly ι S :=
  ∏ e ∈ s, MvPolynomial.eval₂ (SubexponentialSAT.WeightedSupport.scalarHom (ι := ι))
    (fun i => SubexponentialSAT.WeightedSupport.incidenceArgument
      (β e i) (L e i) (zs e i) (rows e i)) (F e)

/-- The original local expansion after the input coordinates have been
substituted. The residue-section values beta no longer occur. -/
def restoredProduct {α : Type*} {σ : α → Type*} (x : ι → S) (s : Finset α)
    (F : ∀ e, MvPolynomial (σ e) S) (L : ∀ e, σ e → MvPolynomial ι S)
    (zs : ∀ e, σ e → Finset ℕ)
    (rows : ∀ e, σ e → ℕ → MvPolynomial ι S) : Polynomial S :=
  ∏ e ∈ s, MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (MvPolynomial.eval x (L e i)) +
      ∑ r ∈ zs e i, Polynomial.monomial r (MvPolynomial.eval x (rows e i r))) (F e)

theorem incidenceProduct_admissible {α : Type*} {σ : α → Type*} (s : Finset α)
    (F : ∀ e, MvPolynomial (σ e) S)
    (β : ∀ e, σ e → S) (L : ∀ e, σ e → MvPolynomial ι S)
    (zs : ∀ e, σ e → Finset ℕ)
    (rows : ∀ e, σ e → ℕ → MvPolynomial ι S)
    (hL : ∀ e ∈ s, ∀ i, (L e i).totalDegree ≤ 1)
    (hpos : ∀ e ∈ s, ∀ i r, r ∈ zs e i → 0 < r)
    (hrows : ∀ e ∈ s, ∀ i r, r ∈ zs e i → (rows e i r).totalDegree ≤ 1) :
    SubexponentialSAT.WeightedSupport.Admissible (incidenceProduct s F β L zs rows) := by
  apply SubexponentialSAT.WeightedSupport.admissible_factor_product
  intro e he i
  exact SubexponentialSAT.WeightedSupport.admissible_incidenceArgument
    (β e i) (L e i) (zs e i) (rows e i)
    (hL e he i) (hpos e he i) (hrows e he i)

theorem evalXU_incidenceProduct {α : Type*} {σ : α → Type*}
    (x : ι → S) (s : Finset α) (F : ∀ e, MvPolynomial (σ e) S)
    (β : ∀ e, σ e → S) (L : ∀ e, σ e → MvPolynomial ι S)
    (zs : ∀ e, σ e → Finset ℕ)
    (rows : ∀ e, σ e → ℕ → MvPolynomial ι S) :
    evalXU x (incidenceProduct s F β L zs rows) = restoredProduct x s F L zs rows := by
  unfold incidenceProduct restoredProduct
  rw [evalXU_factor_product]
  simp only [evalXU_incidenceArgument]

/-- Revised Lemma 4.2 for actual incidence arguments and arbitrary factor
tables. Both the support-degree and high-U hypotheses of the abstract
truncation theorem are derived from local linearity, positive Z order,
divisibility of the lifted defect, and nilpotence of p. -/
theorem incidence_groups_truncation {α : Type*} [DecidableEq α] {σ : α → Type*}
    (x : ι → S) (p : S) (μ D : ℕ) (s₀ s₁ : Finset α)
    (F : ∀ e, MvPolynomial (σ e) S)
    (β : ∀ e, σ e → S) (L : ∀ e, σ e → MvPolynomial ι S)
    (zs : ∀ e, σ e → Finset ℕ)
    (rows : ∀ e, σ e → ℕ → MvPolynomial ι S)
    (hnil : p ^ μ = 0)
    (hL : ∀ e ∈ s₀ ∪ s₁, ∀ i, (L e i).totalDegree ≤ 1)
    (hpos : ∀ e ∈ s₀ ∪ s₁, ∀ i r, r ∈ zs e i → 0 < r)
    (hrows : ∀ e ∈ s₀ ∪ s₁, ∀ i r, r ∈ zs e i → (rows e i r).totalDegree ≤ 1)
    (hdefect : ∀ e ∈ s₀ ∪ s₁, ∀ i, p ∣ MvPolynomial.eval x (L e i) - β e i) :
    evalXU x (canonical μ D (D + μ)
      (canonical μ D (D + μ) (incidenceProduct s₀ F β L zs rows) *
       canonical μ D (D + μ) (incidenceProduct s₁ F β L zs rows))) =
      trunc D (restoredProduct x s₀ F L zs rows * restoredProduct x s₁ F L zs rows) := by
  have hs₀ : s₀ ⊆ s₀ ∪ s₁ := Finset.subset_union_left
  have hs₁ : s₁ ⊆ s₀ ∪ s₁ := Finset.subset_union_right
  have ha₀ := incidenceProduct_admissible s₀ F β L zs rows
    (fun e he => hL e (hs₀ he)) (fun e he => hpos e (hs₀ he))
    (fun e he => hrows e (hs₀ he))
  have ha₁ := incidenceProduct_admissible s₁ F β L zs rows
    (fun e he => hL e (hs₁ he)) (fun e he => hpos e (hs₁ he))
    (fun e he => hrows e (hs₁ he))
  have hd₀ := SubexponentialSAT.NilpotentDefect.powerDivisible_factor_product x p s₀ F β L zs rows
    (fun e he => hdefect e (hs₀ he))
  have hd₁ := SubexponentialSAT.NilpotentDefect.powerDivisible_factor_product x p s₁ F β L zs rows
    (fun e he => hdefect e (hs₁ he))
  have hd : SubexponentialSAT.NilpotentDefect.PowerDivisible (Polynomial.C p)
      ((substX x) (incidenceProduct s₀ F β L zs rows *
        incidenceProduct s₁ F β L zs rows)) := by
    rw [map_mul]
    exact SubexponentialSAT.NilpotentDefect.powerDivisible_mul hd₀ hd₁
  have hn : (Polynomial.C p) ^ μ = (0 : Polynomial S) := by
    simp only [← map_pow, hnil, map_zero]
  have hhigh : ∀ j, μ ≤ j → ((substX x)
      (incidenceProduct s₀ F β L zs rows * incidenceProduct s₁ F β L zs rows)).coeff j = 0 := by
    intro j hj
    exact SubexponentialSAT.NilpotentDefect.high_coeff_eq_zero hd hn j hj
  calc
    _ = trunc D (evalXU x (incidenceProduct s₀ F β L zs rows *
        incidenceProduct s₁ F β L zs rows)) :=
      truncated_groups_substitution x μ D _ _ ha₀ ha₁ hhigh
    _ = _ := by rw [map_mul, evalXU_incidenceProduct, evalXU_incidenceProduct]

/-- For finite linear forms, even the local degree assumptions disappear:
they are proved from the actual coefficient arrays. -/
theorem linear_incidence_groups_truncation
    {α : Type*} [DecidableEq α] {σ : α → Type*}
    (x : ι → S) (p : S) (μ D : ℕ) (s₀ s₁ : Finset α)
    (F : ∀ e, MvPolynomial (σ e) S) (β : ∀ e, σ e → S)
    (coordinates : Finset ι) (a : ∀ e, σ e → ι → S)
    (zs : ∀ e, σ e → Finset ℕ) (b : ∀ e, σ e → ℕ → ι → S)
    (hnil : p ^ μ = 0)
    (hpos : ∀ e ∈ s₀ ∪ s₁, ∀ i r, r ∈ zs e i → 0 < r)
    (hdefect : ∀ e ∈ s₀ ∪ s₁, ∀ i,
      p ∣ MvPolynomial.eval x (SubexponentialSAT.WeightedSupport.linearForm coordinates (a e i)) - β e i) :
    let L := fun e i => SubexponentialSAT.WeightedSupport.linearForm coordinates (a e i)
    let rows := fun e i r => SubexponentialSAT.WeightedSupport.linearForm coordinates (b e i r)
    evalXU x (canonical μ D (D + μ)
      (canonical μ D (D + μ) (incidenceProduct s₀ F β L zs rows) *
       canonical μ D (D + μ) (incidenceProduct s₁ F β L zs rows))) =
      trunc D (restoredProduct x s₀ F L zs rows * restoredProduct x s₁ F L zs rows) := by
  dsimp only
  apply incidence_groups_truncation x p μ D s₀ s₁ F β _ zs _ hnil
  · intro e he i
    exact SubexponentialSAT.WeightedSupport.linearForm_degree coordinates (a e i)
  · exact hpos
  · intro e he i r hr
    exact SubexponentialSAT.WeightedSupport.linearForm_degree coordinates (b e i r)
  · exact hdefect

end Ring

end

end SubexponentialSAT.Truncation

end OAI.Algorithms
