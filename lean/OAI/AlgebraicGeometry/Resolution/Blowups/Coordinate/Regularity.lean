import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialCoefficientOrder
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Noetherian.Basic

/-! # Regularity -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.Regularity.Construction

noncomputable section

/-! Regularity of a coordinate with unit derivative in a Noetherian rational algebra. -/

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

theorem iteratedDerivation_zero (D : Derivation k A A) (j : ℕ) : D^[j] 0 = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply', ih, map_zero]

/-- If multiplication by a coordinate kills an element, every derivative
of that element lies in the coordinate ideal. -/
theorem coordinate_annihilator_derivatives_mem [Algebra ℚ A]
    (D : Derivation k A A) (z : A) (hz : D z = 1) (x : A) (hx : z * x = 0) (j : ℕ) :
    D^[j] x ∈ Ideal.span {z} := by
  have h := congrArg (fun r => D^[j + 1] r) hx
  rw [DifferentialCoefficientOrder.Construction.iteratedDerivation_coordinate_mul D z hz, iteratedDerivation_zero] at h
  have hn : (j + 1) • D^[j] x ∈ Ideal.span {z} := by
    have he : (j + 1) • D^[j] x = -(z * D^[j + 1] x) := eq_neg_of_add_eq_zero_right h
    rw [he]
    exact (Ideal.span {z}).neg_mem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self z))
  obtain ⟨u, hu⟩ := DifferentialCoefficientOrder.Construction.natCast_isUnit_of_rationalAlgebra (A := A) (j + 1) (by omega)
  rw [nsmul_eq_mul, ← hu] at hn
  have hmul := (Ideal.span {z}).mul_mem_left (u⁻¹ : Aˣ) hn
  simpa only [← mul_assoc, Units.inv_mul, one_mul] using hmul

/-- A coordinate is a non-zero-divisor in a Noetherian rational algebra.
The proof uses the derivative order criterion and Krull intersection. -/
theorem coordinate_isRegular [Algebra ℚ A] [IsNoetherianRing A]
    (D : Derivation k A A) (z : A) (hz : D z = 1) : IsRegular z := by
  have hzero : ∀ x : A, z * x = 0 → x = 0 := by
    intro x hx
    let Z : Ideal A := Ideal.span {z}
    have hp : ∀ b : ℕ, x ∈ Z ^ b := by
      intro b
      apply (DifferentialCoefficientOrder.Construction.mem_pow_iff_coordinate_derivatives D z hz Z (Ideal.mem_span_singleton_self z) b x).mpr
      intro j _
      exact Submodule.mem_sup_right (coordinate_annihilator_derivatives_mem D z hz x hx j)
    have hi : x ∈ (⨅ b : ℕ, Z ^ b • ⊤ : Submodule A A) := by
      rw [Submodule.mem_iInf]
      intro b
      simpa only [smul_eq_mul, Ideal.mul_top] using hp b
    obtain ⟨r, hr⟩ := (Z.mem_iInf_smul_pow_eq_bot_iff x).mp hi
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp r.property
    change r.val * x = x at hr
    rw [hs, mul_assoc, mul_left_comm z s x, hx, mul_zero] at hr
    exact hr.symm
  constructor
  · intro x y h
    change z * x = z * y at h
    apply sub_eq_zero.mp
    apply hzero
    rw [mul_sub, h, sub_self]
  · intro x y h
    change x * z = y * z at h
    apply sub_eq_zero.mp
    apply hzero
    rw [mul_sub, mul_comm z x, mul_comm z y, h, sub_self]

/-- A derivation descends through an ideal that it preserves. -/
def quotientDerivation (D : Derivation k A A) (I : Ideal A)
    (hI : ∀ x ∈ I, D x ∈ I) : Derivation k (A ⧸ I) (A ⧸ I) where
  toLinearMap := (I.restrictScalars k).liftQ
    ((Ideal.Quotient.mkₐ k I).toLinearMap.comp D.toLinearMap) (by
      intro x hx
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hI x hx))
  map_one_eq_zero' := by
    change Ideal.Quotient.mk I (D 1) = 0
    rw [D.map_one_eq_zero, map_zero]
  leibniz' x y := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.mk I (D (x * y)) =
      Ideal.Quotient.mk I x * Ideal.Quotient.mk I (D y) +
        Ideal.Quotient.mk I y * Ideal.Quotient.mk I (D x)
    rw [D.leibniz]
    change Ideal.Quotient.mk I (x * D y + y * D x) = _
    rw [map_add, map_mul, map_mul]

theorem quotientDerivation_mk (D : Derivation k A A) (I : Ideal A)
    (hI : ∀ x ∈ I, D x ∈ I) (x : A) :
    quotientDerivation D I hI (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (D x) := rfl

/-- A regular pair can be swapped when its second element is regular
modulo the first. -/
theorem regular_quotient_swap (c z : A) (hc : IsRegular c)
    (hz : IsRegular (Ideal.Quotient.mk (Ideal.span {c}) z)) :
    IsRegular (Ideal.Quotient.mk (Ideal.span {z}) c) := by
  let C : Ideal A := Ideal.span {c}
  let Z : Ideal A := Ideal.span {z}
  have hzero : ∀ x : A ⧸ Z, Ideal.Quotient.mk Z c * x = 0 → x = 0 := by
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hcr : c * r ∈ Z := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rwa [map_mul]
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp hcr
    have hsC : Ideal.Quotient.mk C s = 0 := by
      apply hz.left
      have he := congrArg (Ideal.Quotient.mk C) hs
      have hc0 : Ideal.Quotient.mk C c = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self c)
      simpa only [map_mul, hc0, zero_mul, mul_zero] using he.symm
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hsC)
    have hr : r = z * t := by
      apply hc.left
      change c * r = c * (z * t)
      rw [hs, ht]
      ring
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [hr]
    exact Z.mul_mem_right t (Ideal.mem_span_singleton_self z)
  constructor
  · intro x y h
    change Ideal.Quotient.mk Z c * x = Ideal.Quotient.mk Z c * y at h
    apply sub_eq_zero.mp
    apply hzero
    rw [mul_sub, h, sub_self]
  · intro x y h
    change x * Ideal.Quotient.mk Z c = y * Ideal.Quotient.mk Z c at h
    apply sub_eq_zero.mp
    apply hzero
    rw [mul_sub, mul_comm _ x, mul_comm _ y, h, sub_self]

/-- A regular element annihilated by the coordinate derivation remains
regular on the coordinate hypersurface in a Noetherian rational algebra. -/
theorem regular_mod_coordinate [Algebra ℚ A] [IsNoetherianRing A]
    (D : Derivation k A A) (c z : A) (hc : IsRegular c) (hDc : D c = 0) (hDz : D z = 1) :
    IsRegular (Ideal.Quotient.mk (Ideal.span {z}) c) := by
  let : IsNoetherianRing (A ⧸ Ideal.span {c}) :=
    isNoetherianRing_of_surjective A _ (Ideal.Quotient.mk (Ideal.span {c})) Ideal.Quotient.mk_surjective
  have hI : ∀ x ∈ Ideal.span {c}, D x ∈ Ideal.span {c} := by
    intro x hx
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hx
    rw [ht, D.leibniz, hDc]
    change c * D t + t * 0 ∈ Ideal.span {c}
    rw [mul_zero, add_zero]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self c)
  let E := quotientDerivation D (Ideal.span {c}) hI
  have hz : E (Ideal.Quotient.mk (Ideal.span {c}) z) = 1 := by
    rw [quotientDerivation_mk, hDz, map_one]
  exact regular_quotient_swap c z hc (coordinate_isRegular E _ hz)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.Regularity.Construction
