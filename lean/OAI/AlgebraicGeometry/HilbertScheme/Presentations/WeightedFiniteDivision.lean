import OAI.AlgebraicGeometry.HilbertScheme.Presentations.WeightedPolynomials

/-! # Weighted Finite Division -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.WeightedFiniteDivision.GradedHilbert

noncomputable section

/-! Division by finitely many weighted homogeneous polynomials admits weighted homogeneous remainders without enlarging any leading-term bound. -/

open _root_.MvPolynomial DirectSum
open scoped MonomialOrder

universe u v

variable {K : Type u} [Field K] {n : ℕ}
variable (w : Fin (n + 1) → ℕ)

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem weighted_coordinate_decompose_eq_component (p : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (d : ℕ) :
    (decompose (weightedHomogeneousSubmodule K w) p d).val = weightedHomogeneousComponent w d p := by
  have he : (inferInstance : Decomposition (weightedHomogeneousSubmodule K w)) = MvPolynomial.weightedDecomposition K w := Subsingleton.elim _ _
  exact (congrArg (fun D : Decomposition (weightedHomogeneousSubmodule K w) => (D.decompose' p d).val) he).trans
    (MvPolynomial.weightedDecomposition.decompose'_apply K w p d)

theorem weightedComponent_mul_right (d e : ℕ) (p b : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (hb : b.IsWeightedHomogeneous w e) :
    weightedHomogeneousComponent w d (p * b) =
      (if e ≤ d then weightedHomogeneousComponent w (d - e) p else 0) * b := by
  rw [← weighted_coordinate_decompose_eq_component, ← weighted_coordinate_decompose_eq_component]
  by_cases he : e ≤ d
  · rw [ite_eq_left he]
    change (decompose (weightedHomogeneousSubmodule K w) (p * b) d).val =
      (decompose (weightedHomogeneousSubmodule K w) p (d - e)).val * b
    exact coe_decompose_mul_of_right_mem_of_le (weightedHomogeneousSubmodule K w) hb he
  · rw [ite_eq_right he, zero_mul]
    change (decompose (weightedHomogeneousSubmodule K w) (p * b) d).val = 0
    exact coe_decompose_mul_of_right_mem_of_not_le (weightedHomogeneousSubmodule K w) hb he

theorem weightedComponent_leadingDegree_le (m : MonomialOrder (Fin (n + 1)))
    (d : ℕ) (p : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) : m.degree (weightedHomogeneousComponent w d p) ≼[m] m.degree p := by
  apply m.degree_le_iff.mpr
  intro a ha
  rw [support_weightedHomogeneousComponent] at ha
  exact m.le_degree (Finset.mem_filter.mp ha).1

variable (m : MonomialOrder (Fin (n + 1)))
variable {ι : Type v} [Fintype ι]
variable (b : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (e : ι → ℕ)

theorem weighted_homogeneous_finite_division (hb : ∀ i, (b i).IsWeightedHomogeneous w (e i)) (hb0 : ∀ i, b i ≠ 0)
    (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (d : ℕ) (hf : f.IsWeightedHomogeneous w d) :
    ∃ (q : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (r : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n),
      f = (∑ i, q i * b i) + r ∧ r.IsWeightedHomogeneous w d ∧
      (∀ i, m.degree (q i * b i) ≼[m] m.degree f) ∧
      (∀ a ∈ r.support, ∀ i, ¬ m.degree (b i) ≤ a) := by
  classical
  obtain ⟨q, r, hfr, hq, hr⟩ := m.div (fun i => m.isUnit_leadingCoeff.mpr (hb0 i)) f
  let q' := fun i => if e i ≤ d then weightedHomogeneousComponent w (d - e i) (q i) else 0
  have hproduct (i : ι) : q' i * b i = weightedHomogeneousComponent w d (q i * b i) :=
    (weightedComponent_mul_right w d (e i) (q i) (b i) (hb i)).symm
  refine ⟨q', weightedHomogeneousComponent w d r, ?_, weightedHomogeneousComponent_isWeightedHomogeneous d r, ?_, ?_⟩
  · have hsum : Finsupp.linearCombination (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) b q = ∑ i, q i * b i := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      · rfl
      · intro i
        exact zero_smul _ _
    have he := congrArg (weightedHomogeneousComponent w d) hfr
    rw [weightedHomogeneousComponent_eq_self hf, map_add, hsum, map_sum] at he
    simpa only [← hproduct] using he
  · intro i
    rw [hproduct]
    exact (weightedComponent_leadingDegree_le w m d (q i * b i)).trans (by simpa only [mul_comm] using hq i)
  · intro a ha i
    rw [support_weightedHomogeneousComponent] at ha
    exact hr a (Finset.mem_filter.mp ha).1 i

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.WeightedFiniteDivision.GradedHilbert
