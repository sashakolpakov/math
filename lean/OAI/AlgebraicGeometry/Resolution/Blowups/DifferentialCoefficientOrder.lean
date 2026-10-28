import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialOrder
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Algebra.Rat

/-! # Differential Coefficient Order -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialCoefficientOrder.Construction

noncomputable section

/-!
Coefficient order on a hypersurface with a coordinate derivation. The ambient
ring need not be a polynomial ring over the hypersurface quotient.
-/

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

theorem iteratedDerivation_mem_pow (D : Derivation k A A) (M : Ideal A) (n j : ℕ)
    {p : A} (hp : p ∈ M ^ (n + j)) : D^[j] p ∈ M ^ n := by
  induction j generalizing n with
  | zero => simpa using hp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    apply DifferentialOrder.Construction.derivation_mem_pow D M n
    apply ih (n + 1)
    simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hp

theorem iteratedDerivation_add (D : Derivation k A A) (j : ℕ) (p q : A) :
    D^[j] (p + q) = D^[j] p + D^[j] q := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply', ih, map_add]

/-- Leibniz's formula simplifies when the first factor is a coordinate. -/
theorem iteratedDerivation_coordinate_mul (D : Derivation k A A) (z : A)
    (hz : D z = 1) (q : A) (j : ℕ) :
    D^[j + 1] (z * q) = z * D^[j + 1] q + (j + 1) • D^[j] q := by
  induction j with
  | zero => simp [D.leibniz, hz, Algebra.smul_def]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, map_add, D.leibniz, map_nsmul, hz]
    change z * D (D^[j + 1] q) + D^[j + 1] q * 1 + (j + 1) • D (D^[j] q) =
      z * D^[j + 1 + 1] q + (j + 1 + 1) • D^[j + 1] q
    simp only [mul_one, ← Function.iterate_succ_apply', nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring

/-- Nonzero natural numbers are invertible in a rational algebra. -/
theorem natCast_isUnit_of_rationalAlgebra [Algebra ℚ A] (n : ℕ) (hn : n ≠ 0) :
    IsUnit (n : A) := by
  have hQ : IsUnit (n : ℚ) := isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hn)
  simpa using hQ.map (algebraMap ℚ A)

/-- The first `b` derivatives modulo the coordinate detect order at any
ideal containing that coordinate, also for non-polynomial ambient rings. -/
theorem mem_pow_iff_coordinate_derivatives [Algebra ℚ A]
    (D : Derivation k A A) (z : A) (hz : D z = 1)
    (M : Ideal A) (hzM : z ∈ M) (b : ℕ) (p : A) :
    p ∈ M ^ b ↔ ∀ j < b, D^[j] p ∈ M ^ (b - j) ⊔ Ideal.span {z} := by
  constructor
  · intro hp j hj
    apply Submodule.mem_sup_left
    apply iteratedDerivation_mem_pow D M (b - j) j
    simpa only [Nat.sub_add_cancel (Nat.le_of_lt hj)] using hp
  · induction b generalizing p with
    | zero => simp
    | succ b ih =>
      intro hp
      have hp0 := hp 0 (by omega)
      simp only [Function.iterate_zero, id_eq, Nat.sub_zero] at hp0
      obtain ⟨t, ht, w, hw, htw⟩ := Submodule.mem_sup.mp hp0
      obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hw
      have hpq : p = t + z * q := by rw [← hq]; exact htw.symm
      have hqM : q ∈ M ^ b := by
        apply ih q
        intro j hj
        let N : Ideal A := M ^ (b - j) ⊔ Ideal.span {z}
        have hpd : D^[j + 1] p ∈ N := by
          simpa only [Nat.succ_sub_succ_eq_sub] using hp (j + 1) (by omega)
        have htd : D^[j + 1] t ∈ N := by
          apply Submodule.mem_sup_left
          apply iteratedDerivation_mem_pow D M (b - j) (j + 1)
          convert ht using 1
          congr 1
          omega
        have hzd : z * D^[j + 1] q ∈ N := by
          apply Submodule.mem_sup_right
          exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self z)
        have hn : (j + 1) • D^[j] q ∈ N := by
          rw [hpq, iteratedDerivation_add, iteratedDerivation_coordinate_mul D z hz] at hpd
          have h := N.sub_mem (N.sub_mem hpd htd) hzd
          simpa only [add_sub_cancel_left] using h
        obtain ⟨u, hu⟩ := natCast_isUnit_of_rationalAlgebra (A := A) (j + 1) (by omega)
        rw [nsmul_eq_mul, ← hu] at hn
        have h := N.mul_mem_left (u⁻¹ : Aˣ) hn
        simpa only [← mul_assoc, Units.inv_mul, one_mul] using h
      rw [hpq]
      exact Ideal.add_mem _ ht (by
        rw [pow_succ']
        exact Ideal.mul_mem_mul hzM hqM)

/-- Powers of an ideal on a quotient pull back to the power plus the kernel. -/
theorem quotient_mk_mem_mapped_pow_iff (M N : Ideal A) (n : ℕ) (p : A) :
    Ideal.Quotient.mk N p ∈ M.map (Ideal.Quotient.mk N) ^ n ↔ p ∈ M ^ n ⊔ N := by
  change p ∈ (M.map (Ideal.Quotient.mk N) ^ n).comap (Ideal.Quotient.mk N) ↔ _
  rw [← Ideal.map_pow, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

/-- The derivative criterion expressed directly on the hypersurface quotient. -/
theorem mem_pow_iff_coordinate_quotient_derivatives [Algebra ℚ A]
    (D : Derivation k A A) (z : A) (hz : D z = 1)
    (M : Ideal A) (hzM : z ∈ M) (b : ℕ) (p : A) :
    p ∈ M ^ b ↔ ∀ j < b,
      Ideal.Quotient.mk (Ideal.span {z}) (D^[j] p) ∈
        M.map (Ideal.Quotient.mk (Ideal.span {z})) ^ (b - j) := by
  simp only [quotient_mk_mem_mapped_pow_iff]
  exact mem_pow_iff_coordinate_derivatives D z hz M hzM b p

/-- The `j`th differential coefficient ideal on the hypersurface `z = 0`. -/
def differentialCoefficientIdeal (D : Derivation k A A) (z : A) (J : Ideal A) (j : ℕ) :
    Ideal (A ⧸ Ideal.span {z}) :=
  Ideal.span (Set.range (fun p : J => Ideal.Quotient.mk (Ideal.span {z}) (D^[j] p.val)))

/-- An arbitrary ideal has order at least `b` precisely when its differential
coefficient ideals have orders at least `b-j` on the coordinate hypersurface. -/
theorem ideal_order_iff_differentialCoefficientIdeals [Algebra ℚ A]
    (D : Derivation k A A) (z : A) (hz : D z = 1)
    (J M : Ideal A) (hzM : z ∈ M) (b : ℕ) :
    J ≤ M ^ b ↔ ∀ j < b, differentialCoefficientIdeal D z J j ≤
      M.map (Ideal.Quotient.mk (Ideal.span {z})) ^ (b - j) := by
  constructor
  · intro hJ j hj
    apply Ideal.span_le.mpr
    rintro x ⟨p, rfl⟩
    exact (mem_pow_iff_coordinate_quotient_derivatives D z hz M hzM b p.val).mp
      (hJ p.property) j hj
  · intro h p hp
    apply (mem_pow_iff_coordinate_quotient_derivatives D z hz M hzM b p).mpr
    intro j hj
    apply h j hj
    exact Ideal.subset_span ⟨⟨p, hp⟩, rfl⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialCoefficientOrder.Construction
