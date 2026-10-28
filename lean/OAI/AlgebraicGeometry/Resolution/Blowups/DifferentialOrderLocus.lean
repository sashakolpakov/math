import OAI.AlgebraicGeometry.Resolution.Blowups.PersistentHypersurface
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Differential Order Locus -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialOrderLocus.Construction

noncomputable section

section

/-! Differential equations characterize the polynomial high-order locus in characteristic zero. -/

open _root_.MvPolynomial

variable {R : Type*} [CommRing R]

/-- Failure of a finite power bound determines a smaller exact order. -/
theorem exists_exact_power_below (I : Ideal R) (p : R) (b : ℕ) (hp : p ∉ I ^ b) :
    ∃ n < b, p ∈ I ^ n ∧ p ∉ I ^ (n + 1) := by
  classical
  have hex : ∃ m : ℕ, p ∉ I ^ m := ⟨b, hp⟩
  have hm0 : Nat.find hex ≠ 0 := by
    intro hzero
    have h := Nat.find_spec hex
    simp only [hzero, pow_zero, Ideal.one_eq_top, Submodule.mem_top] at h
    exact h trivial
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hle : Nat.find hex ≤ b := Nat.find_min' hex hp
  refine ⟨n, by omega, ?_, ?_⟩
  · by_contra hbad
    have hmin := Nat.find_min' hex hbad
    omega
  · simpa only [hn, Nat.succ_eq_add_one] using Nat.find_spec hex

/-- Differential ideals increase with the allowed number of derivatives. -/
theorem iteratedDifferentialIdeal_monotone (J : Ideal R) : Monotone (DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J) := by
  apply monotone_nat_of_le_succ
  intro n
  exact DifferentialIdealTransform.Construction.iteratedDifferentialIdeal_mono n (DifferentialIdealTransform.Construction.le_firstDifferentialIdeal J)

variable {σ : Type*}

theorem iteratedPDeriv_append (l m : List σ) (p : MvPolynomial σ R) :
    DifferentialOrder.Construction.iteratedPDeriv (l ++ m) p = DifferentialOrder.Construction.iteratedPDeriv m (DifferentialOrder.Construction.iteratedPDeriv l p) := by
  induction l generalizing p with
  | nil => rfl
  | cons i l ih => exact ih (pderiv i p)

variable {K : Type*} [Field K] [CharZero K]

/-- At a rational point of affine space, order at least `b` is equivalent
to vanishing of every partial derivative of order below `b`. -/
theorem polynomial_mem_point_pow_iff_derivatives (x : σ → K) (p : MvPolynomial σ K) (b : ℕ) :
    p ∈ PolynomialTranslation.Construction.polynomialPointIdeal x ^ b ↔
      ∀ l : List σ, l.length < b → eval x (DifferentialOrder.Construction.iteratedPDeriv l p) = 0 := by
  constructor
  · intro hp l hl
    have hpow : p ∈ PolynomialTranslation.Construction.polynomialPointIdeal x ^ (1 + l.length) :=
      Ideal.pow_le_pow_right (by omega) hp
    have hd := OrderLocus.Construction.iteratedPDeriv_mem_pow l (PolynomialTranslation.Construction.polynomialPointIdeal x) 1 hpow
    rw [pow_one] at hd
    exact hd
  · intro h
    by_contra hp
    obtain ⟨n, hnb, hn, hn1⟩ := exists_exact_power_below (PolynomialTranslation.Construction.polynomialPointIdeal x) p b hp
    cases n with
    | zero =>
      have hzero := h [] (by simpa using hnb)
      apply hn1
      rw [zero_add, pow_one]
      exact hzero
    | succ n =>
      obtain ⟨l, i, hl, _, hi⟩ := PolynomialTranslation.Construction.polynomial_atPoint_derivative_with_nonzero_gradient x n hn hn1
      apply hi
      have hv := h (l ++ [i]) (by simp only [List.length_append, List.length_singleton, hl]; omega)
      simpa only [iteratedPDeriv_append, DifferentialOrder.Construction.iteratedPDeriv] using hv

/-- A polynomial ideal has high order precisely when its corresponding
differential ideal vanishes at the point. This gives equations for the order locus. -/
theorem polynomial_order_locus_iff_differentialIdeal
    (J : Ideal (MvPolynomial σ K)) (x : σ → K) (b : ℕ) :
    J ≤ PolynomialTranslation.Construction.polynomialPointIdeal x ^ (b + 1) ↔
      DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J b ≤ PolynomialTranslation.Construction.polynomialPointIdeal x := by
  constructor
  · intro h
    simpa only [pow_one] using DifferentialIdealTransform.Construction.iteratedDifferentialIdeal_le_pow (PolynomialTranslation.Construction.polynomialPointIdeal x) J 1 b
      (by simpa only [Nat.add_comm 1 b] using h)
  · intro h p hp
    apply (polynomial_mem_point_pow_iff_derivatives x p (b + 1)).mpr
    intro l hl
    apply h
    exact iteratedDifferentialIdeal_monotone J (by omega)
      (PersistentHypersurface.Construction.iteratedPDeriv_mem_differentialIdeal l J hp)

/-- The prime-spectrum point defined by evaluating polynomial coordinates. -/
def polynomialSpectrumPoint (x : σ → K) : PrimeSpectrum (MvPolynomial σ K) :=
  ⟨PolynomialTranslation.Construction.polynomialPointIdeal x, RingHom.ker_isPrime (eval x)⟩

/-- A closed algebraic locus whose rational points have order at least `b+1`. -/
def polynomialDifferentialOrderLocus (J : Ideal (MvPolynomial σ K)) (b : ℕ) :
    Set (PrimeSpectrum (MvPolynomial σ K)) :=
  PrimeSpectrum.zeroLocus (DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J b : Set (MvPolynomial σ K))

omit [CharZero K] in
theorem polynomialDifferentialOrderLocus_isClosed (J : Ideal (MvPolynomial σ K)) (b : ℕ) :
    IsClosed (polynomialDifferentialOrderLocus J b) := PrimeSpectrum.isClosed_zeroLocus _

/-- The closed locus has exactly the required order condition at each rational point. -/
theorem polynomialSpectrumPoint_mem_orderLocus_iff
    (J : Ideal (MvPolynomial σ K)) (b : ℕ) (x : σ → K) :
    polynomialSpectrumPoint x ∈ polynomialDifferentialOrderLocus J b ↔
      J ≤ PolynomialTranslation.Construction.polynomialPointIdeal x ^ (b + 1) := by
  rw [polynomialDifferentialOrderLocus, PrimeSpectrum.mem_zeroLocus]
  exact (polynomial_order_locus_iff_differentialIdeal J x b).symm

end

/-! A finite global differential-order bound for a nonzero polynomial ideal. -/

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

/-- Every nonzero partial derivative has strictly smaller total degree. -/
theorem nonzero_pderiv_totalDegree_lt (p : MvPolynomial σ R) (i : σ) (hi : pderiv i p ≠ 0) :
    (pderiv i p).totalDegree < p.totalDegree := by
  classical
  obtain ⟨d, hd, he⟩ := Finset.exists_mem_eq_sup (pderiv i p).support
    (MvPolynomial.support_nonempty.mpr hi) Finsupp.degree
  have hc : p.coeff (d + Finsupp.single i 1) ≠ 0 := by
    intro hz
    have h := mem_support_iff.mp hd
    rw [coeff_pderiv, hz, zero_mul] at h
    exact h rfl
  have hle := le_totalDegree (mem_support_iff.mpr hc)
  change Finsupp.degree (d + Finsupp.single i 1) ≤ p.totalDegree at hle
  rw [map_add, Finsupp.degree_single] at hle
  change (pderiv i p).totalDegree = Finsupp.degree d at he
  omega

variable {K : Type*} [Field K] [CharZero K]

/-- A nonconstant polynomial over a characteristic-zero field has a nonzero partial derivative. -/
theorem exists_nonzero_pderiv_of_totalDegree_pos (p : MvPolynomial σ K) (hp : 0 < p.totalDegree) :
    ∃ i : σ, pderiv i p ≠ 0 := by
  classical
  have hp0 : p ≠ 0 := by intro h; simp [h] at hp
  obtain ⟨d, hd, he⟩ := Finset.exists_mem_eq_sup p.support
    (MvPolynomial.support_nonempty.mpr hp0) Finsupp.degree
  change p.totalDegree = Finsupp.degree d at he
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, map_zero] at he
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
  have hed : e + Finsupp.single i 1 = d := tsub_add_cancel_of_le hsingle
  have hfactor : (e i : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (e i)
  have hc : (pderiv i p).coeff e ≠ 0 := by
    rw [coeff_pderiv, hed]
    exact mul_ne_zero (mem_support_iff.mp hd) hfactor
  refine ⟨i, ?_⟩
  intro hz
  exact hc (by simp only [hz, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply])

omit [CharZero K] in
/-- A nonzero constant section already makes the ideal the unit ideal. -/
theorem ideal_eq_top_of_nonzero_degree_zero (J : Ideal (MvPolynomial σ K)) (p : MvPolynomial σ K)
    (hpJ : p ∈ J) (hp : p ≠ 0) (hd : p.totalDegree = 0) : J = ⊤ := by
  have he : p = C (p.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp hd
  have hc : p.coeff 0 ≠ 0 := by
    intro hz
    apply hp
    rw [he, hz, C_0]
  apply J.eq_top_of_isUnit_mem hpJ
  rw [he]
  exact (isUnit_iff_ne_zero.mpr hc).map C

/-- At most the total degree of one nonzero section is enough to make
the iterated differential ideal the unit ideal. No Noetherian hypothesis is needed. -/
theorem iteratedDifferentialIdeal_eq_top_of_degree_bound (n : ℕ)
    (J : Ideal (MvPolynomial σ K)) (p : MvPolynomial σ K)
    (hd : p.totalDegree ≤ n) (hpJ : p ∈ J) (hp : p ≠ 0) :
    DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J n = ⊤ := by
  induction n generalizing J p with
  | zero =>
    exact ideal_eq_top_of_nonzero_degree_zero J p hpJ hp (Nat.eq_zero_of_le_zero hd)
  | succ n ih =>
    by_cases hdegree : p.totalDegree = 0
    · have hJ : J = ⊤ := ideal_eq_top_of_nonzero_degree_zero J p hpJ hp hdegree
      apply top_le_iff.mp
      rw [← hJ]
      exact iteratedDifferentialIdeal_monotone J (Nat.zero_le (n + 1))
    · obtain ⟨i, hi⟩ := exists_nonzero_pderiv_of_totalDegree_pos p (Nat.pos_of_ne_zero hdegree)
      have hdi := nonzero_pderiv_totalDegree_lt p i hi
      exact ih (DifferentialIdealTransform.Construction.firstDifferentialIdeal J) (pderiv i p) (by omega)
        (DifferentialIdealTransform.Construction.derivation_mem_firstDifferentialIdeal J (PersistentHypersurface.Construction.polynomialPartialDerivationInt i) hpJ) hi

/-- Every nonzero polynomial ideal has a finite uniform differential-order bound. -/
theorem exists_polynomial_differential_order_bound (J : Ideal (MvPolynomial σ K)) (hJ : J ≠ ⊥) :
    ∃ n : ℕ, DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J n = ⊤ := by
  obtain ⟨p, hpJ, hp⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  exact ⟨p.totalDegree, iteratedDifferentialIdeal_eq_top_of_degree_bound p.totalDegree J p le_rfl hpJ hp⟩

/-- The orders of a nonzero polynomial ideal are bounded uniformly over all rational points. -/
theorem exists_polynomial_uniform_order_bound (J : Ideal (MvPolynomial σ K)) (hJ : J ≠ ⊥) :
    ∃ n : ℕ, ∀ x : σ → K, ¬ J ≤ PolynomialTranslation.Construction.polynomialPointIdeal x ^ (n + 1) := by
  obtain ⟨n, hn⟩ := exists_polynomial_differential_order_bound J hJ
  refine ⟨n, ?_⟩
  intro x hx
  have h := (polynomial_order_locus_iff_differentialIdeal J x n).mp hx
  rw [hn] at h
  have hprime : (PolynomialTranslation.Construction.polynomialPointIdeal x).IsPrime := RingHom.ker_isPrime (eval x)
  exact hprime.ne_top (top_le_iff.mp h)

/-- A nonzero polynomial ideal attains a finite maximum order at a rational
point. The next order locus is empty at all rational points. -/
theorem exists_polynomial_maximum_order (J : Ideal (MvPolynomial σ K)) (hJ : J ≠ ⊥) :
    ∃ (b : ℕ) (x : σ → K), J ≤ PolynomialTranslation.Construction.polynomialPointIdeal x ^ b ∧
      ∀ y : σ → K, ¬ J ≤ PolynomialTranslation.Construction.polynomialPointIdeal y ^ (b + 1) := by
  classical
  obtain ⟨n, hn⟩ := exists_polynomial_uniform_order_bound J hJ
  have hex : ∃ m : ℕ, ∀ y : σ → K, ¬ J ≤ PolynomialTranslation.Construction.polynomialPointIdeal y ^ m := ⟨n + 1, hn⟩
  have hm0 : Nat.find hex ≠ 0 := by
    intro hzero
    have h := Nat.find_spec hex (fun _ => 0)
    rw [hzero, pow_zero, Ideal.one_eq_top] at h
    exact h le_top
  obtain ⟨b, hb⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hnot : ¬ ∀ y : σ → K, ¬ J ≤ PolynomialTranslation.Construction.polynomialPointIdeal y ^ b := by
    intro hy
    have hmin := Nat.find_min' hex hy
    omega
  push Not at hnot
  obtain ⟨x, hx⟩ := hnot
  refine ⟨b, x, hx, ?_⟩
  simpa only [hb, Nat.succ_eq_add_one] using Nat.find_spec hex

end

end OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialOrderLocus.Construction
