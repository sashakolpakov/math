import OAI.NumberTheory.Quaternion.Arithmetic.LocalSquareRoot
import OAI.NumberTheory.Quaternion.Arithmetic.FiniteFieldQuadraticNorm

/-! # Local Binary Norm -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.LocalBinaryNorm

noncomputable section

/-! Lift a binary norm equation from a finite residue field by
quadratic Hensel lifting in one of its two nonsingular coordinates. -/

open scoped Classical
open IsLocalRing

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (R : Subring K) [IsLocalRing R]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem residue_ne_zero_norm_eq_one
    (hbound : ∀ x : R, ‖(x : K)‖ ≤ 1)
    (hres : ∀ x : R, residue R x = 0 ↔ ‖(x : K)‖ < 1)
    {x : R} (hx : residue R x ≠ 0) : ‖(x : K)‖ = 1 :=
  le_antisymm (hbound x) (not_lt.mp (fun h => hx ((hres x).mpr h)))

theorem local_binary_norm_surjective [Finite (ResidueField R)]
    (hbound : ∀ x : R, ‖(x : K)‖ ≤ 1)
    (hres : ∀ x : R, residue R x = 0 ↔ ‖(x : K)‖ < 1)
    (hchar : ringChar (ResidueField R) ≠ 2) (h2 : ‖(2 : K)‖ = 1)
    (a b : R) (ha : ‖(a : K)‖ = 1) (hb : ‖(b : K)‖ = 1) :
    ∃ x y : K, x ^ 2 - (a : K) * y ^ 2 = b := by
  let : Fintype (ResidueField R) := Fintype.ofFinite _
  have hares : residue R a ≠ 0 := by
    intro h
    have hh := (hres a).mp h
    rw [ha] at hh
    exact (lt_irrefl 1) hh
  have hbres : residue R b ≠ 0 := by
    intro h
    have hh := (hres b).mp h
    rw [hb] at hh
    exact (lt_irrefl 1) hh
  obtain ⟨x₀, y₀, hxy, hne⟩ := FiniteFieldQuadraticNorm.finiteField_binary_norm_solution_nonzero hchar
    (residue R a) (residue R b) hares hbres
  obtain ⟨x, rfl⟩ := residue_surjective x₀
  obtain ⟨y, rfl⟩ := residue_surjective y₀
  have hsmall : ‖(x : K) ^ 2 - (a : K) * (y : K) ^ 2 - (b : K)‖ < 1 := by
    have hz : residue R (x ^ 2 - a * y ^ 2 - b) = 0 := by
      rw [map_sub, map_sub, map_pow, map_mul, map_pow, hxy, sub_self]
    exact (hres _).mp hz
  rcases hne with hx | hy
  · have hxnorm := residue_ne_zero_norm_eq_one R hbound hres hx
    have he : ‖(x : K) ^ 2 - ((a : K) * (y : K) ^ 2 + (b : K))‖ < 1 := by
      simpa only [sub_add_eq_sub_sub] using hsmall
    obtain ⟨z, hz, _⟩ := LocalSquareRoot.exists_local_square_root (x : K)
      ((a : K) * (y : K) ^ 2 + (b : K)) hxnorm h2 he
    refine ⟨z, y, ?_⟩
    rw [hz]
    ring
  · have hynorm := residue_ne_zero_norm_eq_one R hbound hres hy
    have ha₀ : (a : K) ≠ 0 := by intro h; simp [h] at ha
    have heq : (y : K) ^ 2 - ((x : K) ^ 2 - (b : K)) / (a : K) =
        -((x : K) ^ 2 - (a : K) * (y : K) ^ 2 - (b : K)) / (a : K) := by
      field_simp
      ring
    have he : ‖(y : K) ^ 2 - ((x : K) ^ 2 - (b : K)) / (a : K)‖ < 1 := by
      rw [heq, norm_div, norm_neg, ha, div_one]
      exact hsmall
    obtain ⟨z, hz, _⟩ := LocalSquareRoot.exists_local_square_root (y : K)
      (((x : K) ^ 2 - (b : K)) / (a : K)) hynorm h2 he
    refine ⟨x, z, ?_⟩
    rw [hz, mul_div_cancel₀ _ ha₀]
    ring

end

end OAI.NumberTheory.Quaternion.Arithmetic.LocalBinaryNorm
