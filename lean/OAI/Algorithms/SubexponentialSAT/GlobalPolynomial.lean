import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Factor
import OAI.Algorithms.SubexponentialSAT.TableInterpolation
import OAI.Algorithms.SubexponentialSAT.WeightedSupport

namespace OAI.Algorithms

/-!
# The global counting polynomial

The polynomial is an actual finite sum of products of multivariate table polynomials
with univariate polynomial substitutions. Degree estimates work over arbitrary
commutative semirings, so in particular they do not assume that the prime-power
coefficient ring is a field or a domain.
-/

namespace SubexponentialSAT.GlobalPolynomial

open scoped BigOperators

variable {C : Type*} [CommSemiring C]

/-- Substitute a univariate polynomial for each variable of a table polynomial. -/
noncomputable def compose {ι : Type*} (f : MvPolynomial ι C)
    (path : ι → Polynomial C) : Polynomial C :=
  MvPolynomial.eval₂ Polynomial.C path f

/-- Individual table degrees and path degrees give a genuine composition bound.
No bound on the composed polynomial is assumed. -/
theorem natDegree_compose_le {ι : Type*} [Fintype ι]
    (f : MvPolynomial ι C) (path : ι → Polynomial C) (d r : ℕ)
    (hf : ∀ i, f.degreeOf i ≤ d) (hp : ∀ i, (path i).natDegree ≤ r) :
    (compose f path).natDegree ≤ Fintype.card ι * d * r := by
  classical
  unfold compose
  rw [MvPolynomial.eval₂_eq']
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro a ha
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  calc
    (∏ i, path i ^ a i).natDegree ≤ ∑ i, (path i ^ a i).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _i : ι, d * r := by
      apply Finset.sum_le_sum
      intro i hi
      exact Polynomial.natDegree_pow_le.trans
        (Nat.mul_le_mul ((MvPolynomial.monomial_le_degreeOf i ha).trans (hf i)) (hp i))
    _ = Fintype.card ι * d * r := by simp [Nat.mul_assoc]

/-- Evaluating after polynomial substitution equals evaluating the table at the
values of the substituted paths. -/
theorem eval_compose {ι : Type*} (f : MvPolynomial ι C)
    (path : ι → Polynomial C) (t : C) :
    (compose f path).eval t = MvPolynomial.eval (fun i => (path i).eval t) f := by
  have he : (Polynomial.evalRingHom t).comp Polynomial.C = RingHom.id C := by
    ext c
    simp
  change (Polynomial.evalRingHom t) (MvPolynomial.eval₂ Polynomial.C path f) = _
  rw [MvPolynomial.eval₂_comp_left, he]
  rfl

/-- Univariate composition passes through multivariate table substitution. -/
theorem comp_compose {ι : Type*} (f : MvPolynomial ι C)
    (path : ι → Polynomial C) (q : Polynomial C) :
    (compose f path).comp q = compose f (fun i => (path i).comp q) := by
  have he : (Polynomial.compRingHom q).comp Polynomial.C = Polynomial.C := by
    ext c
    simp
  change (Polynomial.compRingHom q) (MvPolynomial.eval₂ Polynomial.C path f) = _
  rw [MvPolynomial.eval₂_comp_left, he]
  rfl

/-- The polynomial H: sum over assignments of the product over all factors. -/
noncomputable def globalPolynomial {E X : Type*} [Fintype E] [Fintype X]
    {ι : E → Type*} (table : (e : E) → MvPolynomial (ι e) C)
    (path : X → (e : E) → ι e → Polynomial C) : Polynomial C :=
  ∑ x, ∏ e, compose (table e) (path x e)

/-- Evaluation commutes with the finite sum and product defining H. -/
theorem eval_globalPolynomial {E X : Type*} [Fintype E] [Fintype X]
    {ι : E → Type*} (table : (e : E) → MvPolynomial (ι e) C)
    (path : X → (e : E) → ι e → Polynomial C) (t : C) :
    (globalPolynomial table path).eval t =
      ∑ x, ∏ e, MvPolynomial.eval (fun i => (path x e i).eval t) (table e) := by
  classical
  simp only [globalPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_prod,
    eval_compose]

/-- In particular q = X + C θ expresses H(θ+Z) as the corresponding
sum of products with every incidence path shifted by θ. -/
theorem comp_globalPolynomial {E X : Type*} [Fintype E] [Fintype X]
    {ι : E → Type*} (table : (e : E) → MvPolynomial (ι e) C)
    (path : X → (e : E) → ι e → Polynomial C) (q : Polynomial C) :
    (globalPolynomial table path).comp q =
      globalPolynomial table (fun x e i => (path x e i).comp q) := by
  classical
  simp only [globalPolynomial, Polynomial.sum_comp, Polynomial.prod_comp, comp_compose]

/-- Equation (4.2), with d later instantiated by p−1. The number of assignments
never enters the degree bound. -/
theorem natDegree_globalPolynomial_le {E X : Type*} [Fintype E] [Fintype X]
    {ι : E → Type*} [∀ e, Fintype (ι e)]
    (table : (e : E) → MvPolynomial (ι e) C)
    (path : X → (e : E) → ι e → Polynomial C) (k d r : ℕ)
    (hcard : ∀ e, Fintype.card (ι e) ≤ k)
    (htable : ∀ e i, (table e).degreeOf i ≤ d)
    (hpath : ∀ x e i, (path x e i).natDegree ≤ r) :
    (globalPolynomial table path).natDegree ≤ Fintype.card E * k * d * r := by
  classical
  unfold globalPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro x hx
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc
    ∑ e, (compose (table e) (path x e)).natDegree ≤ ∑ _e : E, k * d * r := by
      apply Finset.sum_le_sum
      intro e he
      exact (natDegree_compose_le (table e) (path x e) d r (htable e) (hpath x e)).trans
        (Nat.mul_le_mul_right r (Nat.mul_le_mul_right d (hcard e)))
    _ = Fintype.card E * k * d * r := by simp [Nat.mul_assoc]

/-- An evaluation-at-zero interface for arbitrary finite tables. -/
theorem eval_zero_globalPolynomial {E X : Type*} [Fintype E] [Fintype X]
    {ι : E → Type*} (table : (e : E) → MvPolynomial (ι e) C)
    (path : X → (e : E) → ι e → Polynomial C)
    (values : X → (e : E) → ι e → C) (factor : X → E → C)
    (hpath : ∀ x e i, (path x e i).eval 0 = values x e i)
    (htable : ∀ x e, MvPolynomial.eval (values x e) (table e) = factor x e) :
    (globalPolynomial table path).eval 0 = ∑ x, ∏ e, factor x e := by
  classical
  rw [eval_globalPolynomial]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.prod_congr rfl
  intro e he
  simpa only [hpath] using htable x e

/-- The value is the image of the natural-number sum of products under the
canonical map into the coefficient ring. -/
theorem eval_zero_eq_nat_sum {E X : Type*} [Fintype E] [Fintype X]
    {ι : E → Type*} (table : (e : E) → MvPolynomial (ι e) C)
    (path : X → (e : E) → ι e → Polynomial C)
    (values : X → (e : E) → ι e → C) (factor : X → E → ℕ)
    (hpath : ∀ x e i, (path x e i).eval 0 = values x e i)
    (htable : ∀ x e, MvPolynomial.eval (values x e) (table e) = (factor x e : C)) :
    (globalPolynomial table path).eval 0 = ((∑ x, ∏ e, factor x e : ℕ) : C) := by
  rw [eval_zero_globalPolynomial table path values (fun x e => (factor x e : C))
    hpath htable]
  simp

/-- The strict QD budget used for interpolation, derived from the local
degree bounds and the factor-count bound. -/
theorem natDegree_globalPolynomial_lt {E X : Type*} [Fintype E] [Fintype X]
    {ι : E → Type*} [∀ e, Fintype (ι e)]
    (table : (e : E) → MvPolynomial (ι e) C)
    (path : X → (e : E) → ι e → Polynomial C) (k d r Δ D Q : ℕ)
    (hcard : ∀ e, Fintype.card (ι e) ≤ k)
    (htable : ∀ e i, (table e).degreeOf i ≤ d)
    (hpath : ∀ x e i, (path x e i).natDegree ≤ r)
    (hm : Fintype.card E ≤ Δ * D) (hD : 0 < D)
    (hbudget : Δ * k * d * r < Q) :
    (globalPolynomial table path).natDegree < Q * D := by
  calc
    (globalPolynomial table path).natDegree ≤ Fintype.card E * k * d * r :=
      natDegree_globalPolynomial_le table path k d r hcard htable hpath
    _ ≤ (Δ * D) * k * d * r :=
      Nat.mul_le_mul_right r (Nat.mul_le_mul_right d (Nat.mul_le_mul_right k hm))
    _ = D * (Δ * k * d * r) := by ac_rfl
    _ < D * Q := Nat.mul_lt_mul_of_pos_left hbudget hD
    _ = Q * D := Nat.mul_comm D Q

/-- The scalar polynomial obtained by applying a polynomial row to coordinates. -/
noncomputable def rowValue {V : Type*} [Fintype V]
    (row : V → Polynomial C) (x : V → C) : Polynomial C :=
  ∑ v, Polynomial.C (x v) * row v

theorem comp_rowValue {V : Type*} [Fintype V]
    (row : V → Polynomial C) (x : V → C) (q : Polynomial C) :
    (rowValue row x).comp q = rowValue (fun v => (row v).comp q) x := by
  classical
  simp only [rowValue, Polynomial.sum_comp, Polynomial.mul_comp, Polynomial.C_comp]

theorem coeff_rowValue {V : Type*} [Fintype V]
    (row : V → Polynomial C) (x : V → C) (n : ℕ) :
    (rowValue row x).coeff n = ∑ v, x v * (row v).coeff n := by
  classical
  simp only [rowValue, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]

/-- The scalar coefficient is evaluation of a genuine linear form in X. -/
theorem coeff_rowValue_eq_eval_linearForm {V : Type*} [Fintype V]
    (row : V → Polynomial C) (x : V → C) (n : ℕ) :
    (rowValue row x).coeff n =
      MvPolynomial.eval x (WeightedSupport.linearForm Finset.univ
        (fun v => (row v).coeff n)) := by
  classical
  rw [coeff_rowValue]
  simp [WeightedSupport.linearForm, MvPolynomial.eval_monomial, mul_comm]

/-- Translation does not increase univariate degree, even with zero divisors. -/
theorem natDegree_shift_le (p : Polynomial C) (θ : C) :
    (p.comp (Polynomial.X + Polynomial.C θ)).natDegree ≤ p.natDegree := by
  have hq : (Polynomial.X + Polynomial.C θ : Polynomial C).natDegree ≤ 1 :=
    (Polynomial.natDegree_add_le _ _).trans (max_le Polynomial.natDegree_X_le (by simp))
  exact Polynomial.natDegree_comp_le.trans
    (by simpa using Nat.mul_le_mul_left p.natDegree hq)

/-- Finite positive-degree expansion with the constant coefficient separated. -/
theorem eq_C_add_sum_monomial_of_natDegree_le (p : Polynomial C) (r : ℕ)
    (hp : p.natDegree ≤ r) :
    p = Polynomial.C (p.coeff 0) +
      ∑ n ∈ (Finset.range (r + 1)).erase 0, Polynomial.monomial n (p.coeff n) := by
  classical
  calc
    p = ∑ n ∈ Finset.range (r + 1), Polynomial.monomial n (p.coeff n) :=
      p.as_sum_range' (r + 1) (Nat.lt_succ_of_le hp)
    _ = Polynomial.monomial 0 (p.coeff 0) +
        ∑ n ∈ (Finset.range (r + 1)).erase 0, Polynomial.monomial n (p.coeff n) :=
      (Finset.add_sum_erase _ _ (by simp : 0 ∈ Finset.range (r + 1))).symm
    _ = _ := by rw [Polynomial.monomial_zero_left]

/-- Coefficients can be lifted through a surjective ring map while preserving
the degree bound and any prescribed lift of the constant coefficient. This is
the lifting step used to retain the exact coordinate selector at T = 0. -/
theorem exists_coefficient_lift_with_constant {S : Type*} [CommSemiring S]
    (φ : C →+* S) (hφ : Function.Surjective φ) (p : Polynomial S)
    (c : C) (hc : φ c = p.coeff 0) :
    ∃ q : Polynomial C, q.map φ = p ∧ q.coeff 0 = c ∧ q.natDegree ≤ p.natDegree := by
  classical
  choose lift hlift using hφ
  let s := (Finset.range (p.natDegree + 1)).erase 0
  let tail : Polynomial C := ∑ n ∈ s, Polynomial.monomial n (lift (p.coeff n))
  let q : Polynomial C := Polynomial.C c + tail
  have htail0 : tail.coeff 0 = 0 := by
    rw [show tail = ∑ n ∈ s, Polynomial.monomial n (lift (p.coeff n)) from rfl,
      Polynomial.finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro n hn
    have hn0 : n ≠ 0 := (Finset.mem_erase.mp hn).1
    simp [Polynomial.coeff_monomial, hn0]
  have htailDegree : tail.natDegree ≤ p.natDegree := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro n hn
    exact (Polynomial.natDegree_monomial_le _).trans
      (Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_erase.mp hn).2))
  refine ⟨q, ?_, ?_, ?_⟩
  · simpa [q, tail, s, Polynomial.map_sum, hlift, hc] using
      (eq_C_add_sum_monomial_of_natDegree_le p p.natDegree le_rfl).symm
  · simp [q, htail0]
  · exact (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) htailDegree)

/-- Taking the linear form does not introduce a factor of the ambient dimension
into the path-degree bound. -/
theorem natDegree_rowValue_le {V : Type*} [Fintype V]
    (row : V → Polynomial C) (x : V → C) (r : ℕ)
    (hrow : ∀ v, (row v).natDegree ≤ r) :
    (rowValue row x).natDegree ≤ r := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro v hv
  exact (Polynomial.natDegree_C_mul_le _ _).trans (hrow v)

/-- The concrete shifted-row expansion needed by the symbolic incidence
argument: all coefficients are evaluations of linear forms in the input. -/
theorem shifted_rowValue_expansion {V : Type*} [Fintype V]
    (row : V → Polynomial C) (x : V → C) (θ : C) (r : ℕ)
    (hrow : ∀ v, (row v).natDegree ≤ r) :
    (rowValue row x).comp (Polynomial.X + Polynomial.C θ) =
      Polynomial.C (MvPolynomial.eval x (WeightedSupport.linearForm Finset.univ
        (fun v => ((row v).comp (Polynomial.X + Polynomial.C θ)).coeff 0))) +
      ∑ n ∈ (Finset.range (r + 1)).erase 0,
        Polynomial.monomial n (MvPolynomial.eval x
          (WeightedSupport.linearForm Finset.univ
            (fun v => ((row v).comp (Polynomial.X + Polynomial.C θ)).coeff n))) := by
  rw [comp_rowValue]
  have hd : (rowValue (fun v => (row v).comp (Polynomial.X + Polynomial.C θ)) x).natDegree
      ≤ r := natDegree_rowValue_le _ _ r
        (fun v => (natDegree_shift_le (row v) θ).trans (hrow v))
  simpa only [coeff_rowValue_eq_eval_linearForm] using
    eq_C_add_sum_monomial_of_natDegree_le
      (rowValue (fun v => (row v).comp (Polynomial.X + Polynomial.C θ)) x) r hd

/-- A row equal to the coordinate selector at zero recovers that coordinate. -/
theorem eval_zero_rowValue {V : Type*} [Fintype V] [DecidableEq V]
    (row : V → Polynomial C) (x : V → C) (v : V)
    (hrow : ∀ w, (row w).eval 0 = if w = v then 1 else 0) :
    (rowValue row x).eval 0 = x v := by
  classical
  simp [rowValue, Polynomial.eval_finsetSum, hrow]

/-- The source's sum of products using genuine polynomial rows, rather than
arbitrary assignment-dependent scalar paths. -/
noncomputable def rowGlobalPolynomial {V E A : Type*}
    [DecidableEq V] [Fintype V] [Fintype E] [Fintype A] {ι : E → Type*}
    (table : (e : E) → MvPolynomial (ι e) C)
    (row : (e : E) → ι e → V → Polynomial C) (lift : A → C) : Polynomial C :=
  globalPolynomial table
    (fun (x : V → A) e i => rowValue (row e i) (fun v => lift (x v)))

/-- The polynomial-row form of the global degree bound. -/
theorem natDegree_rowGlobalPolynomial_le {V E A : Type*}
    [DecidableEq V] [Fintype V] [Fintype E] [Fintype A] {ι : E → Type*}
    [∀ e, Fintype (ι e)]
    (table : (e : E) → MvPolynomial (ι e) C)
    (row : (e : E) → ι e → V → Polynomial C) (lift : A → C)
    (k d r : ℕ) (hcard : ∀ e, Fintype.card (ι e) ≤ k)
    (htable : ∀ e i, (table e).degreeOf i ≤ d)
    (hrow : ∀ e i v, (row e i v).natDegree ≤ r) :
    (rowGlobalPolynomial table row lift).natDegree ≤ Fintype.card E * k * d * r := by
  classical
  unfold rowGlobalPolynomial
  apply natDegree_globalPolynomial_le table _ k d r hcard htable
  intro x e i
  exact natDegree_rowValue_le _ _ r (hrow e i)

/-- Exact table interpolation and paths with the correct value at zero recover
the finite factor count, as an element of the coefficient ring. -/
theorem eval_zero_eq_factor_count {V E A : Type*}
    [DecidableEq V] [Fintype V] [Fintype E] [Fintype A]
    (F : Factor.System V E A) (lift : A → C)
    (table : (e : E) → MvPolynomial {v // v ∈ F.scope e} C)
    (path : (V → A) → (e : E) → {v // v ∈ F.scope e} → Polynomial C)
    (hpath : ∀ x e v, (path x e v).eval 0 = lift (x v.1))
    (htable : ∀ e (a : {v // v ∈ F.scope e} → A),
      MvPolynomial.eval (fun v => lift (a v)) (table e) =
        if F.table e a = true then 1 else 0) :
    (globalPolynomial table path).eval 0 = (Factor.count F : C) := by
  classical
  change (globalPolynomial table path).eval 0 =
    ((∑ x : V → A, ∏ e, Factor.factorValue F e x : ℕ) : C)
  apply eval_zero_eq_nat_sum table path (fun x e v => lift (x v.1))
    (fun x e => Factor.factorValue F e x) hpath
  intro x e
  rw [htable e (fun v => x v.1)]
  by_cases h : F.table e (fun v => x v.1) = true <;>
    simp [Factor.factorValue, Factor.evalFactor, h]

/-- The same count identity for the source's polynomial-row construction. -/
theorem eval_zero_row_eq_factor_count {V E A : Type*}
    [DecidableEq V] [Fintype V] [Fintype E] [Fintype A]
    (F : Factor.System V E A) (lift : A → C)
    (table : (e : E) → MvPolynomial {v // v ∈ F.scope e} C)
    (row : (e : E) → {v // v ∈ F.scope e} → V → Polynomial C)
    (hrow : ∀ e v w, (row e v w).eval 0 = if w = v.1 then 1 else 0)
    (htable : ∀ e (a : {v // v ∈ F.scope e} → A),
      MvPolynomial.eval (fun v => lift (a v)) (table e) =
        if F.table e a = true then 1 else 0) :
    (rowGlobalPolynomial table row lift).eval 0 = (Factor.count F : C) := by
  classical
  unfold rowGlobalPolynomial
  apply eval_zero_eq_factor_count F lift table _ _ htable
  intro x e v
  exact eval_zero_rowValue _ _ v.1 (hrow e v)

section Interpolated

variable {R : Type*} [CommRing R]

/-- The explicit tensor-product Lagrange interpolant of a Boolean factor. -/
noncomputable def interpolatedTable {V E A : Type*} [DecidableEq V] [Fintype A]
    (F : Factor.System V E A) (lift : A → R)
    (hu : TableInterpolation.UnitDifferences lift) (e : E) :
    MvPolynomial {v // v ∈ F.scope e} R := by
  classical
  exact TableInterpolation.mvInterpolate lift hu
    (fun a => if F.table e a = true then 1 else 0)

theorem eval_interpolatedTable {V E A : Type*} [DecidableEq V] [Fintype A]
    (F : Factor.System V E A) (lift : A → R)
    (hu : TableInterpolation.UnitDifferences lift) (e : E)
    (a : {v // v ∈ F.scope e} → A) :
    MvPolynomial.eval (fun v => lift (a v)) (interpolatedTable F lift hu e) =
      if F.table e a = true then 1 else 0 := by
  classical
  exact TableInterpolation.eval_mvInterpolate lift hu _ a

theorem degreeOf_interpolatedTable_le {V E A : Type*} [DecidableEq V] [Fintype A]
    (F : Factor.System V E A) (lift : A → R)
    (hu : TableInterpolation.UnitDifferences lift) (e : E)
    (v : {v // v ∈ F.scope e}) :
    (interpolatedTable F lift hu e).degreeOf v ≤ Fintype.card A - 1 := by
  classical
  exact TableInterpolation.degreeOf_mvInterpolate_le lift hu _ v

/-- The source's H, with the factor polynomials constructed by interpolation. -/
noncomputable def interpolatedGlobalPolynomial {V E A : Type*}
    [DecidableEq V] [Fintype V] [Fintype E] [Fintype A]
    (F : Factor.System V E A) (lift : A → R)
    (hu : TableInterpolation.UnitDifferences lift)
    (row : (e : E) → {v // v ∈ F.scope e} → V → Polynomial R) : Polynomial R :=
  rowGlobalPolynomial (interpolatedTable F lift hu) row lift

/-- H(0) is the exact factor count in the coefficient ring. -/
theorem eval_zero_interpolatedGlobalPolynomial {V E A : Type*}
    [DecidableEq V] [Fintype V] [Fintype E] [Fintype A]
    (F : Factor.System V E A) (lift : A → R)
    (hu : TableInterpolation.UnitDifferences lift)
    (row : (e : E) → {v // v ∈ F.scope e} → V → Polynomial R)
    (hrow : ∀ e v w, (row e v w).eval 0 = if w = v.1 then 1 else 0) :
    (interpolatedGlobalPolynomial F lift hu row).eval 0 = (Factor.count F : R) := by
  exact eval_zero_row_eq_factor_count F lift (interpolatedTable F lift hu) row hrow
    (eval_interpolatedTable F lift hu)

/-- The actual interpolated H satisfies the global degree bound. Its factor
degrees are proved from Lagrange interpolation, not postulated. -/
theorem natDegree_interpolatedGlobalPolynomial_le {V E A : Type*}
    [DecidableEq V] [Fintype V] [Fintype E] [Fintype A]
    (F : Factor.System V E A) (lift : A → R)
    (hu : TableInterpolation.UnitDifferences lift)
    (row : (e : E) → {v // v ∈ F.scope e} → V → Polynomial R)
    (k r : ℕ) (harity : ∀ e, (F.scope e).card ≤ k)
    (hrow : ∀ e v w, (row e v w).natDegree ≤ r) :
    (interpolatedGlobalPolynomial F lift hu row).natDegree ≤
      Fintype.card E * k * (Fintype.card A - 1) * r := by
  apply natDegree_rowGlobalPolynomial_le _ _ _ k (Fintype.card A - 1) r
    _ (degreeOf_interpolatedTable_le F lift hu) hrow
  intro e
  simpa using harity e

/-- Literal integer-label specialization of both conclusions in Section 4.1.
The result constructs H and proves the displayed m*k*(p−1)*r bound. -/
theorem integerLabel_globalPolynomial_spec {V E : Type*}
    [DecidableEq V] [Fintype V] [Fintype E]
    (p k r : ℕ) (F : Factor.System V E (Fin p))
    (hu : TableInterpolation.UnitDifferences (fun i : Fin p => (i.val : R)))
    (row : (e : E) → {v // v ∈ F.scope e} → V → Polynomial R)
    (harity : ∀ e, (F.scope e).card ≤ k)
    (hzero : ∀ e v w, (row e v w).eval 0 = if w = v.1 then 1 else 0)
    (hdegree : ∀ e v w, (row e v w).natDegree ≤ r) :
    (interpolatedGlobalPolynomial F (fun i => (i.val : R)) hu row).eval 0 =
        (Factor.count F : R) ∧
      (interpolatedGlobalPolynomial F (fun i => (i.val : R)) hu row).natDegree ≤
        Fintype.card E * k * (p - 1) * r := by
  constructor
  · exact eval_zero_interpolatedGlobalPolynomial F _ hu row hzero
  · simpa only [Fintype.card_fin] using
      natDegree_interpolatedGlobalPolynomial_le F _ hu row k r harity hdegree

end Interpolated

end SubexponentialSAT.GlobalPolynomial

end OAI.Algorithms
