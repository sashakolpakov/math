import OAI.NumberTheory.ArithmeticGroups.Lattices.IntegerWeightDerivation
import OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.Eigencomponents

/-! # Integer Weight Components -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.IntegerWeightComponents.Construction

noncomputable section

section

/-! A subspace stable under an integer Euler derivation contains each
weighted homogeneous component of all its polynomials. -/

open scoped Classical
open _root_.MvPolynomial

theorem integerWeightDerivation_component
    {k σ : Type*} [Field k] [Fintype σ] (w : σ → ℤ)
    (p : MvPolynomial σ k) (z : ℤ) :
    IntegerWeightDerivation.Construction.integerWeightDerivation w (weightedHomogeneousComponent w z p) =
      (z : k) • weightedHomogeneousComponent w z p := by
  rw [weightedHomogeneousComponent_apply, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [IntegerWeightDerivation.Construction.integerWeightDerivation_monomial, (Finset.mem_filter.mp hm).2]

theorem sum_integerWeightComponents
    {k σ : Type*} [Field k] [Fintype σ] (w : σ → ℤ) (p : MvPolynomial σ k) :
    ∑ z ∈ p.support.image (Finsupp.weight w), weightedHomogeneousComponent w z p = p := by
  ext m
  rw [coeff_sum]
  simp only [coeff_weightedHomogeneousComponent, Finset.sum_ite_eq]
  by_cases hm : p.coeff m = 0
  · simp only [hm, ite_self]
  · rw [ite_eq_left (Finset.mem_image.mpr ⟨m, MvPolynomial.mem_support_iff.mpr hm, rfl⟩)]

theorem integerWeightComponent_mem_of_invariant
    {k σ : Type*} [Field k] [CharZero k] [Fintype σ] (w : σ → ℤ)
    (W : Submodule k (MvPolynomial σ k))
    (hW : ∀ p ∈ W, IntegerWeightDerivation.Construction.integerWeightDerivation w p ∈ W)
    {p : MvPolynomial σ k} (hp : p ∈ W) (z : ℤ) :
    weightedHomogeneousComponent w z p ∈ W := by
  let S := p.support.image (Finsupp.weight w)
  have hs : ∑ i ∈ S, weightedHomogeneousComponent w i p ∈ W := by
    rw [sum_integerWeightComponents]
    exact hp
  by_cases hz : z ∈ S
  · exact Finite.Eigencomponents.Construction.finite_eigencomponents_mem (IntegerWeightDerivation.Construction.integerWeightDerivation (k := k) w).toLinearMap W hW
      (fun i : ℤ => (i : k)) Int.cast_injective S (fun i => weightedHomogeneousComponent w i p)
      (integerWeightDerivation_component w p) hs z hz
  · have he : weightedHomogeneousComponent w z p = 0 := by
      rw [weightedHomogeneousComponent_apply]
      apply Finset.sum_eq_zero
      intro m hm
      exact (hz (Finset.mem_image.mpr ⟨m, (Finset.mem_filter.mp hm).1, (Finset.mem_filter.mp hm).2⟩)).elim
    rw [he]
    exact W.zero_mem

end

/-! Scaling variables by integer powers acts by the total integer
weight on a weighted homogeneous polynomial. -/

open scoped Classical
open _root_.MvPolynomial

theorem prod_unit_integer_weights
    {K σ : Type*} [Field K] [Fintype σ] (t : Kˣ) (w : σ → ℤ) (m : σ →₀ ℕ) :
    (∏ i, ((t ^ w i : Kˣ) : K) ^ m i) = ((t ^ Finsupp.weight w m : Kˣ) : K) := by
  have h (s : Finset σ) : (∏ i ∈ s, (t ^ w i) ^ m i) = t ^ (∑ i ∈ s, (m i : ℤ) * w i) := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.prod_empty, Finset.sum_empty, zpow_zero]
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add]
      congr 1
      rw [mul_comm, zpow_mul, zpow_natCast]
  have he := congrArg (fun u : Kˣ => (u : K)) (h Finset.univ)
  simpa only [Units.coe_prod, Units.val_pow_eq_pow_val, Finsupp.weight_eq_sum, nsmul_eq_mul] using he

theorem eval_integer_scaled_monomial
    {k K σ : Type*} [Field k] [Field K] [Fintype σ]
    (v : k →+* K) (t : Kˣ) (w : σ → ℤ) (x : σ → K) (m : σ →₀ ℕ) (c : k) :
    MvPolynomial.eval₂Hom v (fun i => ((t ^ w i : Kˣ) : K) * x i) (monomial m c) =
      ((t ^ Finsupp.weight w m : Kˣ) : K) * MvPolynomial.eval₂Hom v x (monomial m c) := by
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial]
  have hl : (m.prod fun i e => (((t ^ w i : Kˣ) : K) * x i) ^ e) =
      ∏ i, (((t ^ w i : Kˣ) : K) * x i) ^ m i := m.prod_fintype _ (fun _ => pow_zero _)
  have hr : (m.prod fun i e => x i ^ e) = ∏ i, x i ^ m i := m.prod_fintype _ (fun _ => pow_zero _)
  rw [hl, hr]
  simp only [mul_pow, Finset.prod_mul_distrib, prod_unit_integer_weights]
  ring

theorem eval_integer_scaled_homogeneous
    {k K σ : Type*} [Field k] [Field K] [Fintype σ]
    (v : k →+* K) (t : Kˣ) (w : σ → ℤ) (x : σ → K)
    (p : MvPolynomial σ k) (z : ℤ) (hp : p.IsWeightedHomogeneous w z) :
    MvPolynomial.eval₂Hom v (fun i => ((t ^ w i : Kˣ) : K) * x i) p =
      ((t ^ z : Kˣ) : K) * MvPolynomial.eval₂Hom v x p := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [eval_integer_scaled_monomial, hp (MvPolynomial.mem_support_iff.mp hm)]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.IntegerWeightComponents.Construction
