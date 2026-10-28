import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialCoefficientOrder
import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialIdealTransform

/-! # Euler Order Criterion -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.EulerOrderCriterion.Construction

noncomputable section

/-! Differential order criteria from an Euler derivation on a coordinate ideal. -/

variable {A : Type*} [CommRing A]

/-- A derivation fixing the generators and taking all values in their
ideal induces the identity on the ideal modulo its square. -/
theorem euler_span_mod_square (E : Derivation ℤ A A) (s : Set A)
    (hEs : ∀ x ∈ s, E x = x) (hE : ∀ x, E x ∈ Ideal.span s)
    {p : A} (hp : p ∈ Ideal.span s) : E p - p ∈ Ideal.span s ^ 2 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
  · intro x hx
    rw [hEs x hx, sub_self]
    exact Ideal.zero_mem _
  · rw [map_zero, sub_self]
    exact Ideal.zero_mem _
  · intro x y _ _ hx hy
    convert (Ideal.span s ^ 2).add_mem hx hy using 1
    rw [map_add]
    ring
  · intro a x hx ih
    change E (a * x) - a * x ∈ Ideal.span s ^ 2
    have h1 := (Ideal.span s ^ 2).mul_mem_left a ih
    have h2 : x * E a ∈ Ideal.span s ^ 2 := by
      simpa only [pow_two] using Ideal.mul_mem_mul hx (hE a)
    convert (Ideal.span s ^ 2).add_mem h1 h2 using 1
    rw [E.leibniz]
    change a * E x + x * E a - a * x = _
    ring

/-- On the `n`th associated graded piece, the Euler derivation acts by multiplication by `n`. -/
theorem euler_ideal_power_congruence (E : Derivation ℤ A A) (M : Ideal A)
    (hE : ∀ x, E x ∈ M) (hM : ∀ x ∈ M, E x - x ∈ M ^ 2)
    (n : ℕ) {p : A} (hp : p ∈ M ^ n) : E p - n • p ∈ M ^ (n + 1) := by
  induction n generalizing p with
  | zero => simpa only [zero_nsmul, sub_zero, zero_add, pow_one] using hE p
  | succ n ih =>
    rw [pow_succ] at hp
    refine Submodule.mul_induction_on hp ?_ ?_
    · intro x hx y hy
      have h1 : x * (E y - y) ∈ M ^ (n + 1 + 1) := by
        simpa only [← pow_add] using Ideal.mul_mem_mul hx (hM y hy)
      have h2 : y * (E x - n • x) ∈ M ^ (n + 1 + 1) := by
        rw [pow_succ']
        exact Ideal.mul_mem_mul hy (ih hx)
      convert (M ^ (n + 1 + 1)).add_mem h1 h2 using 1
      rw [E.leibniz]
      change x * E y + y * E x - (n + 1) • (x * y) = _
      simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring
    · intro x y hx hy
      convert (M ^ (n + 1 + 1)).add_mem hx hy using 1
      rw [map_add, nsmul_add]
      ring

variable {ι : Type*} [Fintype ι]

/-- The radial derivation determined by coordinate functions and their partial derivations. -/
def coordinateEulerDerivation (z : ι → A) (D : ι → Derivation ℤ A A) : Derivation ℤ A A :=
  ∑ i, z i • D i

theorem coordinateEulerDerivation_apply (z : ι → A) (D : ι → Derivation ℤ A A) (p : A) :
    coordinateEulerDerivation z D p = ∑ i, z i * D i p := by
  have h := congrArg (fun f : A → A => f p)
    (map_sum (Derivation.coeFnAddMonoidHom : Derivation ℤ A A →+ A → A)
      (fun i => z i • D i) Finset.univ)
  simpa only [coordinateEulerDerivation, Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply,
    Derivation.smul_apply, smul_eq_mul] using h

/-- The radial derivation maps a section of any ideal into the coordinate
ideal times the first differential ideal of that ideal. -/
theorem coordinateEulerDerivation_mem_product (z : ι → A) (D : ι → Derivation ℤ A A)
    (J : Ideal A) {p : A} (hp : p ∈ J) :
    coordinateEulerDerivation z D p ∈ Ideal.span (Set.range z) * DifferentialIdealTransform.Construction.firstDifferentialIdeal J := by
  rw [coordinateEulerDerivation_apply]
  apply Ideal.sum_mem
  intro i _
  exact Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) (DifferentialIdealTransform.Construction.derivation_mem_firstDifferentialIdeal J (D i) hp)

theorem coordinateEulerDerivation_mem_span (z : ι → A) (D : ι → Derivation ℤ A A) (p : A) :
    coordinateEulerDerivation z D p ∈ Ideal.span (Set.range z) := by
  rw [coordinateEulerDerivation_apply]
  apply Ideal.sum_mem
  intro i _
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- Partial derivations dual to the coordinate functions give the required Euler eigenvectors. -/
theorem coordinateEulerDerivation_coordinate [DecidableEq ι]
    (z : ι → A) (D : ι → Derivation ℤ A A)
    (hD : ∀ i j, D i (z j) = if i = j then 1 else 0) (j : ι) :
    coordinateEulerDerivation z D (z j) = z j := by
  rw [coordinateEulerDerivation_apply]
  simp [hD, mul_ite]

/-- With coordinate generators and their dual derivations, differential
ideals characterize order in any rational algebra, without a polynomial-ring assumption. -/
theorem coordinate_ideal_order_iff_differentialIdeal [Algebra ℚ A] [DecidableEq ι]
    (z : ι → A) (D : ι → Derivation ℤ A A)
    (hD : ∀ i j, D i (z j) = if i = j then 1 else 0) (J : Ideal A) (b : ℕ) :
    J ≤ Ideal.span (Set.range z) ^ (b + 1) ↔
      DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J b ≤ Ideal.span (Set.range z) := by
  let M : Ideal A := Ideal.span (Set.range z)
  let E := coordinateEulerDerivation z D
  have hE : ∀ p, E p ∈ M := coordinateEulerDerivation_mem_span z D
  have hM : ∀ p ∈ M, E p - p ∈ M ^ 2 := by
    intro p hp
    apply euler_span_mod_square E (Set.range z) _ hE hp
    rintro x ⟨i, rfl⟩
    exact coordinateEulerDerivation_coordinate z D hD i
  change J ≤ M ^ (b + 1) ↔ DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J b ≤ M
  constructor
  · intro h
    simpa only [pow_one] using DifferentialIdealTransform.Construction.iteratedDifferentialIdeal_le_pow M J 1 b
      (by simpa only [Nat.add_comm 1 b] using h)
  · induction b generalizing J with
    | zero =>
      intro h
      simpa only [DifferentialIdealTransform.Construction.iteratedDifferentialIdeal, zero_add, pow_one] using h
    | succ b ih =>
      intro h
      have hfirst : DifferentialIdealTransform.Construction.firstDifferentialIdeal J ≤ M ^ (b + 1) := ih (DifferentialIdealTransform.Construction.firstDifferentialIdeal J) h
      intro p hp
      have hpM : p ∈ M ^ (b + 1) := hfirst (DifferentialIdealTransform.Construction.le_firstDifferentialIdeal J hp)
      have hEp : E p ∈ M ^ (b + 1 + 1) := by
        rw [pow_succ']
        exact Ideal.mul_mono le_rfl hfirst (coordinateEulerDerivation_mem_product z D J hp)
      have hcong := euler_ideal_power_congruence E M hE hM (b + 1) hpM
      have hnp : (b + 1) • p ∈ M ^ (b + 1 + 1) := by
        simpa only [sub_sub_cancel] using (M ^ (b + 1 + 1)).sub_mem hEp hcong
      obtain ⟨u, hu⟩ := DifferentialCoefficientOrder.Construction.natCast_isUnit_of_rationalAlgebra (A := A) (b + 1) (by omega)
      rw [nsmul_eq_mul, ← hu] at hnp
      have hmul := (M ^ (b + 1 + 1)).mul_mem_left (u⁻¹ : Aˣ) hnp
      simpa only [← mul_assoc, Units.inv_mul, one_mul] using hmul

end

end OAI.AlgebraicGeometry.Resolution.Blowups.EulerOrderCriterion.Construction
