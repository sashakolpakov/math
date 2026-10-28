import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.Ideal

/-! # Differential Order -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialOrder.Construction

/-! Differential estimates for ideal orders in the characteristic-zero resolution argument. -/

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

/-- A derivation lowers membership in powers of any ideal by at most one. -/
theorem derivation_mem_pow (D : Derivation k A A) (I : Ideal A) (n : ℕ)
    {r : A} (hr : r ∈ I ^ (n + 1)) : D r ∈ I ^ n := by
  induction n generalizing r with
  | zero => simp
  | succ n ih =>
    rw [pow_succ] at hr
    refine Submodule.mul_induction_on hr ?_ ?_
    · intro x hx y hy
      rw [D.leibniz]
      change x * D y + y * D x ∈ I ^ (n + 1)
      apply Ideal.add_mem
      · exact (I ^ (n + 1)).mul_mem_right (D y) hx
      · simpa only [pow_succ', Nat.succ_eq_add_one] using Ideal.mul_mem_mul hy (ih hx)
    · intro x y hx hy
      rw [map_add]
      exact Ideal.add_mem _ hx hy

variable {σ K : Type*} [Fintype σ] [Field K] [CharZero K]

/-- In characteristic zero, a nonzero homogeneous polynomial of positive
degree has a nonzero partial derivative of one lower degree. -/
theorem homogeneous_exists_nonzero_pderiv {p : MvPolynomial σ K} {n : ℕ}
    (hp : p.IsHomogeneous n) (hp0 : p ≠ 0) (hn : 0 < n) :
    ∃ i : σ, MvPolynomial.pderiv i p ≠ 0 ∧
      (MvPolynomial.pderiv i p).IsHomogeneous (n - 1) := by
  classical
  by_contra h
  push Not at h
  have hzero : ∀ i : σ, MvPolynomial.pderiv i p = 0 := by
    intro i
    by_contra hi
    exact h i hi hp.pderiv
  have he := hp.sum_X_mul_pderiv
  simp only [hzero, mul_zero, Finset.sum_const_zero] at he
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hsmul : (n : K) • p = 0 := by
    simpa only [Nat.cast_smul_eq_nsmul] using he.symm
  exact hp0 ((smul_eq_zero.mp hsmul).resolve_left hnK)

omit [Fintype σ] in
/-- A polynomial of positive exact order at the origin has a partial
derivative of exactly one lower order in characteristic zero. -/
theorem polynomial_exists_pderiv_exact_order {p : MvPolynomial σ K} {n : ℕ}
    (hn : 0 < n) (hp : p ∈ MvPolynomial.idealOfVars σ K ^ n)
    (hp1 : p ∉ MvPolynomial.idealOfVars σ K ^ (n + 1)) :
    ∃ i : σ, MvPolynomial.pderiv i p ∈ MvPolynomial.idealOfVars σ K ^ (n - 1) ∧
      MvPolynomial.pderiv i p ∉ MvPolynomial.idealOfVars σ K ^ n := by
  classical
  have hcoeffs := (MvPolynomial.mem_pow_idealOfVars_iff n p).mp hp
  rw [MvPolynomial.mem_pow_idealOfVars_iff] at hp1
  push Not at hp1
  obtain ⟨d, hd, hdn⟩ := hp1
  have hdegree : Finsupp.degree d = n := by
    have := hcoeffs d hd
    omega
  have hd0 : d ≠ 0 := by
    intro hzero
    simp only [hzero, map_zero] at hdegree
    omega
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd0
  have hdi : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hsingle : Finsupp.single i 1 ≤ d := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Finsupp.single_eq_same] using Nat.one_le_iff_ne_zero.mpr hdi
    · simp [Finsupp.single_eq_of_ne hji]
  let e := d - Finsupp.single i 1
  have he : e + Finsupp.single i 1 = d := tsub_add_cancel_of_le hsingle
  have hedegree : Finsupp.degree e + 1 = n := by
    rw [← Finsupp.degree_single i 1, ← map_add, he, hdegree]
  have hfactor : ((e i : K) + 1) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (e i)
  have hc : AddMonoidAlgebra.coeff ((MvPolynomial.pderiv i p)) (e) ≠ 0 := by
    rw [MvPolynomial.coeff_pderiv, he]
    exact mul_ne_zero (MvPolynomial.mem_support_iff.mp hd) hfactor
  refine ⟨i, ?_, ?_⟩
  · apply derivation_mem_pow (MvPolynomial.pderiv i) (MvPolynomial.idealOfVars σ K) (n - 1)
    simpa only [Nat.sub_add_cancel (Nat.succ_le_of_lt hn)] using hp
  · intro hmem
    have hle := (MvPolynomial.mem_pow_idealOfVars_iff n _).mp hmem e
      (MvPolynomial.mem_support_iff.mpr hc)
    omega

/-- Successive formal partial derivatives, in the order specified by the list. -/
noncomputable def iteratedPDeriv {σ R : Type*} [CommSemiring R] :
    List σ → MvPolynomial σ R → MvPolynomial σ R
  | [], p => p
  | i :: l, p => iteratedPDeriv l (MvPolynomial.pderiv i p)

omit [Fintype σ] in
/-- Repeated differentiation supplies an order-one polynomial after exactly
`n` derivatives of a polynomial of order `n + 1`. -/
theorem polynomial_exists_orderOne_derivative (n : ℕ) {p : MvPolynomial σ K}
    (hp : p ∈ MvPolynomial.idealOfVars σ K ^ (n + 1))
    (hp1 : p ∉ MvPolynomial.idealOfVars σ K ^ (n + 2)) :
    ∃ l : List σ, l.length = n ∧
      Construction.iteratedPDeriv l p ∈ MvPolynomial.idealOfVars σ K ∧
      Construction.iteratedPDeriv l p ∉ MvPolynomial.idealOfVars σ K ^ 2 := by
  induction n generalizing p with
  | zero => exact ⟨[], rfl, by simpa only [Construction.iteratedPDeriv, Nat.zero_add, pow_one] using hp, hp1⟩
  | succ n ih =>
    obtain ⟨i, hi, hi1⟩ := polynomial_exists_pderiv_exact_order
      (p := p) (n := n + 2) (by omega) hp hp1
    have hi' : MvPolynomial.pderiv i p ∈ MvPolynomial.idealOfVars σ K ^ (n + 1) := by
      simpa only [show n + 2 - 1 = n + 1 by omega] using hi
    obtain ⟨l, hl, hmem, hnot⟩ := ih hi' hi1
    exact ⟨i :: l, by simp [hl], hmem, hnot⟩

/-- Vanishing at the origin is exactly membership in the ideal of variables. -/
theorem mem_idealOfVars_iff_constantCoeff_eq_zero {σ R : Type*} [CommSemiring R]
    (p : MvPolynomial σ R) :
    p ∈ MvPolynomial.idealOfVars σ R ↔ MvPolynomial.constantCoeff p = 0 := by
  rw [← pow_one (MvPolynomial.idealOfVars σ R), MvPolynomial.mem_pow_idealOfVars_iff']
  change (∀ d, Finsupp.degree d < 1 → AddMonoidAlgebra.coeff (p) (d) = 0) ↔
    AddMonoidAlgebra.coeff (p) (0) = 0
  constructor
  · intro h
    exact h 0 (by simp)
  · intro h d hd
    have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
    simpa only [hd0] using h

omit [Fintype σ] in
/-- An equation of exact order one vanishes at the origin and has a nonzero
partial derivative there. -/
theorem orderOne_nonzero_gradient {p : MvPolynomial σ K}
    (hp : p ∈ MvPolynomial.idealOfVars σ K)
    (hp2 : p ∉ MvPolynomial.idealOfVars σ K ^ 2) :
    MvPolynomial.constantCoeff p = 0 ∧
      ∃ i : σ, MvPolynomial.constantCoeff (MvPolynomial.pderiv i p) ≠ 0 := by
  refine ⟨(mem_idealOfVars_iff_constantCoeff_eq_zero p).mp hp, ?_⟩
  obtain ⟨i, _, hi⟩ := polynomial_exists_pderiv_exact_order
    (p := p) (n := 1) (by decide) (by simpa only [pow_one] using hp) hp2
  refine ⟨i, ?_⟩
  intro hz
  apply hi
  simpa only [pow_one] using
    (mem_idealOfVars_iff_constantCoeff_eq_zero (MvPolynomial.pderiv i p)).mpr hz

omit [Fintype σ] in
/-- Differentiating a polynomial of order `n + 1` exactly `n` times produces
an equation vanishing at the origin with nonzero gradient there. -/
theorem polynomial_exists_derivative_with_nonzero_gradient (n : ℕ) {p : MvPolynomial σ K}
    (hp : p ∈ MvPolynomial.idealOfVars σ K ^ (n + 1))
    (hp1 : p ∉ MvPolynomial.idealOfVars σ K ^ (n + 2)) :
    ∃ (l : List σ) (i : σ), l.length = n ∧
      MvPolynomial.constantCoeff (Construction.iteratedPDeriv l p) = 0 ∧
      MvPolynomial.constantCoeff (MvPolynomial.pderiv i (Construction.iteratedPDeriv l p)) ≠ 0 := by
  obtain ⟨l, hl, hmem, hnot⟩ := polynomial_exists_orderOne_derivative n hp hp1
  obtain ⟨hz, i, hi⟩ := orderOne_nonzero_gradient hmem hnot
  exact ⟨l, i, hl, hz, hi⟩

end OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialOrder.Construction
