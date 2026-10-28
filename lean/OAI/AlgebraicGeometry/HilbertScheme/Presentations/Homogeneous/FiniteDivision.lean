import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.Polynomials

/-! # Finite Division -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.FiniteDivision.GradedHilbert

noncomputable section

/-! Division by finitely many homogeneous polynomials admits homogeneous remainders without enlarging any leading-term bound. -/

open _root_.MvPolynomial DirectSum
open scoped MonomialOrder

universe u v

variable {K : Type u} [Field K] {n : ℕ}

theorem coordinate_decompose_eq_homogeneousComponent (p : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (d : ℕ) :
    (decompose (Hilbert.Polynomial.GradedHilbert.grading K n) p d).val = homogeneousComponent d p := by
  have he : (inferInstance : Decomposition (Hilbert.Polynomial.GradedHilbert.grading K n)) = MvPolynomial.decomposition := Subsingleton.elim _ _
  exact (congrArg (fun D : Decomposition (Hilbert.Polynomial.GradedHilbert.grading K n) => (D.decompose' p d).val) he).trans
    (MvPolynomial.decomposition.decompose'_apply p d)

theorem homogeneousComponent_mul_right (d e : ℕ) (p b : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (hb : b.IsHomogeneous e) :
    homogeneousComponent d (p * b) =
      (if e ≤ d then homogeneousComponent (d - e) p else 0) * b := by
  rw [← coordinate_decompose_eq_homogeneousComponent, ← coordinate_decompose_eq_homogeneousComponent]
  by_cases he : e ≤ d
  · rw [ite_eq_left he]
    change (decompose (Hilbert.Polynomial.GradedHilbert.grading K n) (p * b) d).val =
      (decompose (Hilbert.Polynomial.GradedHilbert.grading K n) p (d - e)).val * b
    exact coe_decompose_mul_of_right_mem_of_le (Hilbert.Polynomial.GradedHilbert.grading K n) hb he
  · rw [ite_eq_right he, zero_mul]
    change (decompose (Hilbert.Polynomial.GradedHilbert.grading K n) (p * b) d).val = 0
    exact coe_decompose_mul_of_right_mem_of_not_le (Hilbert.Polynomial.GradedHilbert.grading K n) hb he

theorem homogeneousComponent_leadingDegree_le (m : MonomialOrder (Fin (n + 1)))
    (d : ℕ) (p : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) : m.degree (homogeneousComponent d p) ≼[m] m.degree p := by
  apply m.degree_le_iff.mpr
  intro a ha
  rw [support_homogeneousComponent] at ha
  exact m.le_degree (Finset.mem_filter.mp ha).1

variable (m : MonomialOrder (Fin (n + 1)))
variable {ι : Type v} [Fintype ι]
variable (b : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (e : ι → ℕ)

theorem homogeneous_finite_division (hb : ∀ i, (b i).IsHomogeneous (e i)) (hb0 : ∀ i, b i ≠ 0)
    (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (d : ℕ) (hf : f.IsHomogeneous d) :
    ∃ (q : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (r : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n),
      f = (∑ i, q i * b i) + r ∧ r.IsHomogeneous d ∧
      (∀ i, m.degree (q i * b i) ≼[m] m.degree f) ∧
      (∀ a ∈ r.support, ∀ i, ¬ m.degree (b i) ≤ a) := by
  classical
  obtain ⟨q, r, hfr, hq, hr⟩ := m.div (fun i => m.isUnit_leadingCoeff.mpr (hb0 i)) f
  let q' := fun i => if e i ≤ d then homogeneousComponent (d - e i) (q i) else 0
  have hproduct (i : ι) : q' i * b i = homogeneousComponent d (q i * b i) :=
    (homogeneousComponent_mul_right d (e i) (q i) (b i) (hb i)).symm
  refine ⟨q', homogeneousComponent d r, ?_, homogeneousComponent_isHomogeneous d r, ?_, ?_⟩
  · have hsum : Finsupp.linearCombination (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) b q = ∑ i, q i * b i := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      · rfl
      · intro i
        exact zero_smul _ _
    have he := congrArg (homogeneousComponent d) hfr
    rw [homogeneousComponent_eq_self hf, map_add, hsum, map_sum] at he
    simpa only [← hproduct] using he
  · intro i
    rw [hproduct]
    exact (homogeneousComponent_leadingDegree_le m d (q i * b i)).trans (by simpa only [mul_comm] using hq i)
  · intro a ha i
    rw [support_homogeneousComponent] at ha
    exact hr a (Finset.mem_filter.mp ha).1 i

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.FiniteDivision.GradedHilbert
