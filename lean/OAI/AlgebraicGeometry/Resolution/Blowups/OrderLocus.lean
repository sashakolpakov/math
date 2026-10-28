import OAI.AlgebraicGeometry.Resolution.Blowups.PolynomialTranslation

/-! # Order Locus -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.OrderLocus.Construction

/-! Derivative equations containing polynomial loci of high ideal order. -/

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

/-- Each partial derivative lowers the guaranteed ideal power by at most one. -/
theorem iteratedPDeriv_mem_pow (l : List σ) (I : Ideal (MvPolynomial σ R)) (n : ℕ)
    {p : MvPolynomial σ R} (hp : p ∈ I ^ (n + l.length)) :
    DifferentialOrder.Construction.iteratedPDeriv l p ∈ I ^ n := by
  induction l generalizing p with
  | nil => simpa only [DifferentialOrder.Construction.iteratedPDeriv, List.length_nil, Nat.add_zero] using hp
  | cons i l ih =>
    change DifferentialOrder.Construction.iteratedPDeriv l (pderiv i p) ∈ I ^ n
    apply ih
    apply DifferentialOrder.Construction.derivation_mem_pow (pderiv i) I (n + l.length)
    simpa only [List.length_cons, Nat.add_assoc] using hp

/-- An iterated derivative of a section of an ideal vanishes wherever
the ideal order exceeds the number of derivatives. -/
theorem iteratedPDeriv_vanishes_on_orderLocus
    (J : Ideal (MvPolynomial σ R)) (p : J) (l : List σ) (a : σ → R)
    (hJ : J ≤ PolynomialTranslation.Construction.polynomialPointIdeal a ^ (l.length + 1)) :
    eval a (DifferentialOrder.Construction.iteratedPDeriv l p.val) = 0 := by
  have hp : p.val ∈ PolynomialTranslation.Construction.polynomialPointIdeal a ^ (1 + l.length) := by
    simpa only [Nat.add_comm 1 l.length] using hJ p.property
  have hd := iteratedPDeriv_mem_pow l (PolynomialTranslation.Construction.polynomialPointIdeal a) 1 hp
  rw [pow_one] at hd
  exact hd

variable {K : Type*} [Field K] [CharZero K]

/-- At a point of exact ideal order `n + 1`, a derivative of an actual ideal
section gives an equation with nonzero gradient that contains the entire
locus of order at least `n + 1`. -/
theorem exists_gradient_equation_containing_orderLocus
    (J : Ideal (MvPolynomial σ K)) (a : σ → K) (n : ℕ)
    (hJ : J ≤ PolynomialTranslation.Construction.polynomialPointIdeal a ^ (n + 1))
    (hJ1 : ¬ J ≤ PolynomialTranslation.Construction.polynomialPointIdeal a ^ (n + 2)) :
    ∃ (p : J) (l : List σ) (i : σ), l.length = n ∧
      eval a (DifferentialOrder.Construction.iteratedPDeriv l p.val) = 0 ∧
      eval a (pderiv i (DifferentialOrder.Construction.iteratedPDeriv l p.val)) ≠ 0 ∧
      ∀ y : σ → K, J ≤ PolynomialTranslation.Construction.polynomialPointIdeal y ^ (n + 1) →
        eval y (DifferentialOrder.Construction.iteratedPDeriv l p.val) = 0 := by
  change ¬ ∀ p, p ∈ J → p ∈ PolynomialTranslation.Construction.polynomialPointIdeal a ^ (n + 2) at hJ1
  push Not at hJ1
  obtain ⟨p, hp, hp1⟩ := hJ1
  obtain ⟨l, i, hl, hz, hi⟩ :=
    PolynomialTranslation.Construction.polynomial_atPoint_derivative_with_nonzero_gradient a n (hJ hp) hp1
  refine ⟨⟨p, hp⟩, l, i, hl, hz, hi, ?_⟩
  intro y hy
  apply iteratedPDeriv_vanishes_on_orderLocus J ⟨p, hp⟩ l y
  simpa only [hl] using hy

end OAI.AlgebraicGeometry.Resolution.Blowups.OrderLocus.Construction
