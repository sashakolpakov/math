import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.FiniteType

/-! # Type Characters -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Finite.TypeCharacters.Constructions

noncomputable section

/-! Algebraically closed field-valued characters separate nonzero elements
of actual reduced finite-type algebras. This will detect the genuine
irreducibility of products of algebraic cycle supports. -/

variable (k A : Type*) [Field k] [IsAlgClosed k] [CommRing A]
  [Algebra k A] [Algebra.FiniteType k A] [IsReduced A]

theorem exists_character_ne_zero (a : A) (ha : a ≠ 0) :
    ∃ χ : A →ₐ[k] k, χ a ≠ 0 := by
  classical
  by_contra! h
  let : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)
  have hj : a ∈ (⊥ : Ideal A).jacobson := by
    apply Ideal.mem_sInf.mpr
    intro m hm
    let : m.IsMaximal := hm.2
    let : Field (A ⧸ m) := Ideal.Quotient.field m
    let : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
    let φ : (A ⧸ m) →ₐ[k] k := IsAlgClosed.lift
    have hz : Ideal.Quotient.mk m a = 0 :=
      φ.injective ((h (φ.comp (Ideal.Quotient.mkₐ k m))).trans (map_zero φ).symm)
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz
  rw [← Ideal.radical_eq_jacobson, Ideal.radical_bot_of_isReduced, Ideal.mem_bot] at hj
  exact ha hj

theorem character_ext (a b : A) (h : ∀ χ : A →ₐ[k] k, χ a = χ b) : a = b := by
  by_contra hab
  obtain ⟨χ, hχ⟩ := exists_character_ne_zero k A (a - b) (sub_ne_zero.mpr hab)
  apply hχ
  rw [map_sub, h χ, sub_self]

variable [IsDomain A]

theorem exists_character_two_ne_zero (a b : A) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ χ : A →ₐ[k] k, χ a ≠ 0 ∧ χ b ≠ 0 := by
  obtain ⟨χ, hχ⟩ := exists_character_ne_zero k A (a * b) (mul_ne_zero ha hb)
  rw [map_mul, mul_ne_zero_iff] at hχ
  exact ⟨χ, hχ⟩

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Finite.TypeCharacters.Constructions
