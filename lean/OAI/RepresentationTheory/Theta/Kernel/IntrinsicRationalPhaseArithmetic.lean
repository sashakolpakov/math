import Mathlib

/-! # Intrinsic Rational Phase Arithmetic -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicRationalPhaseArithmetic.Intrinsic

noncomputable section

/-! Denominator clearing for a rational bilinear form on a finite
integer lattice. A sufficiently deep lattice translation changes its
quadratic value by an even integer. -/

open scoped Classical BigOperators

theorem finite_denominator {I : Type} [Fintype I] (a : I → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∀ i, ∃ z : ℤ, (D : ℚ) * a i = z := by
  let D := ∏ i, (a i).den
  refine ⟨D, Finset.prod_pos (fun i _ => (a i).den_pos), ?_⟩
  intro i
  obtain ⟨m,hm⟩ : (a i).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  refine ⟨(m : ℤ) * (a i).num, ?_⟩
  calc
    (D : ℚ) * a i = (m : ℚ) * ((a i).den * a i) := by rw [hm, Nat.cast_mul]; ring
    _ = _ := by rw [(a i).den_mul_eq_num]; push_cast; rfl

theorem bilinear_basis_expansion {I V : Type} [Fintype I]
    [AddCommGroup V] (b : Module.Basis I ℤ V)
    (B : V →ₗ[ℤ] V →ₗ[ℤ] ℚ) (u v : V) :
    B u v = ∑ i, ∑ j, (b.repr u i : ℚ) * (b.repr v j : ℚ) * B (b i) (b j) := by
  calc
    B u v = B (∑ i, b.repr u i • b i) (∑ j, b.repr v j • b j) := by
      rw [b.sum_repr, b.sum_repr]
    _ = _ := by
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
        zsmul_eq_mul, Finset.mul_sum]
      conv_lhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem bilinear_integer_denominator {I V : Type} [Fintype I]
    [AddCommGroup V] (b : Module.Basis I ℤ V)
    (B : V →ₗ[ℤ] V →ₗ[ℤ] ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∀ u v : V, ∃ z : ℤ, (D : ℚ) * B u v = z := by
  obtain ⟨D,hD,hcoeff⟩ := finite_denominator (fun ij : I × I => B (b ij.1) (b ij.2))
  choose c hc using hcoeff
  refine ⟨D,hD,?_⟩
  intro u v
  refine ⟨∑ i, ∑ j, b.repr u i * b.repr v j * c (i,j), ?_⟩
  rw [bilinear_basis_expansion b B u v, Finset.mul_sum]
  simp only [Finset.mul_sum, Int.cast_sum, Int.cast_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  calc
    (D : ℚ) * ((b.repr u i : ℚ) * (b.repr v j : ℚ) * B (b i) (b j)) =
        (b.repr u i : ℚ) * (b.repr v j : ℚ) * ((D : ℚ) * B (b i) (b j)) := by ring
    _ = _ := by rw [hc (i,j)]

theorem quadratic_even_difference {V : Type} [AddCommGroup V]
    (B : V →ₗ[ℤ] V →ₗ[ℤ] ℚ) (D : ℕ)
    (hD : ∀ u v : V, ∃ z : ℤ, (D : ℚ) * B u v = z) (u v : V) :
    ∃ z : ℤ, B (u + (2 * (D : ℤ)) • v) (u + (2 * (D : ℤ)) • v) - B u u = 2 * z := by
  obtain ⟨a,ha⟩ := hD u v
  obtain ⟨b,hb⟩ := hD v u
  obtain ⟨c,hc⟩ := hD v v
  refine ⟨a + b + 2 * (D : ℤ) * c, ?_⟩
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
    zsmul_eq_mul, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
  linear_combination 2 * ha + 2 * hb + 4 * (D : ℚ) * hc

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicRationalPhaseArithmetic.Intrinsic
