import OAI.LinearAlgebra.Moore.Outer

/-! The arbitrary-rank-one determinant segment and its exact energy integral. -/

noncomputable section

namespace OAI.LinearAlgebra.Moore

open Matrix OAI.Analysis.Calculus.Quaternion
open scoped MatrixOrder ComplexOrder

theorem mooreDet_outer_zero (n : ℕ) (v : Fin (n + 2) → Quaternion ℝ) :
    mooreDet (n + 2) (OAI.Analysis.Calculus.Quaternion.outer v) = 0 := by
  rw [← columnExtension_projector v (0 : Fin (n + 2)), mooreDet_congruence,
    mooreDet_coordinateProjector_zero, mul_zero]

theorem mooreDet_outer_pencil (n : ℕ)
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) (Quaternion ℝ))
    (v : Fin (n + 2) → Quaternion ℝ) (t s : ℝ) :
    mooreDet (n + 2) (t • A + s • OAI.Analysis.Calculus.Quaternion.outer v) =
      t ^ (n + 2) * mooreDet (n + 2) A +
      s * t ^ (n + 1) * mooreDifferential (n + 2) A (OAI.Analysis.Calculus.Quaternion.outer v) := by
  by_cases ht : t = 0
  · simp [ht, mooreDet_smul, mooreDet_outer_zero]
  · have hm : t • A + s • OAI.Analysis.Calculus.Quaternion.outer v = t • (A + (s / t) • OAI.Analysis.Calculus.Quaternion.outer v) := by
      rw [smul_add, smul_smul]
      congr 1
      rw [mul_div_cancel₀ s ht]
    rw [hm, mooreDet_smul, mooreDet_add_outer_differential]
    have hpow : t ^ (n + 2) = t ^ (n + 1) * t := pow_succ t (n + 1)
    rw [hpow]
    field_simp

theorem mooreDet_outer_segment (n : ℕ)
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) (Quaternion ℝ))
    (v : Fin (n + 2) → Quaternion ℝ) (t : ℝ) :
    mooreDet (n + 2) (t • A + (1 - t) • OAI.Analysis.Calculus.Quaternion.outer v) =
      t ^ (n + 2) * mooreDet (n + 2) A +
      (1 - t) * t ^ (n + 1) * mooreDifferential (n + 2) A (OAI.Analysis.Calculus.Quaternion.outer v) :=
  mooreDet_outer_pencil n A v t (1 - t)

theorem integral_mooreDet_outer_segment (n : ℕ)
    (A : Matrix (Fin (n + 2)) (Fin (n + 2)) (Quaternion ℝ))
    (v : Fin (n + 2) → Quaternion ℝ) :
    (∫ t in (0 : ℝ)..1, mooreDet (n + 2) (t • A + (1 - t) • OAI.Analysis.Calculus.Quaternion.outer v)) =
      mooreDet (n + 2) A / ((n : ℝ) + 3) +
      mooreDifferential (n + 2) A (OAI.Analysis.Calculus.Quaternion.outer v) / (((n : ℝ) + 2) * ((n : ℝ) + 3)) := by
  have hf : (fun t : ℝ ↦ mooreDet (n + 2) (t • A + (1 - t) • OAI.Analysis.Calculus.Quaternion.outer v)) =
      fun t ↦ t ^ ((n + 1) + 1) * mooreDet (n + 2) A +
        t ^ (n + 1) * (1 - t) * mooreDifferential (n + 2) A (OAI.Analysis.Calculus.Quaternion.outer v) := by
    funext t
    rw [mooreDet_outer_segment]
    ring
  rw [hf, OAI.Analysis.PDE.Energy.integral_segment]
  norm_num [Nat.cast_add, Nat.cast_one]
  congr 2 <;> ring

theorem mooreDifferential_outer_nonneg {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (v : Fin n → Quaternion ℝ)
    (hA : (complexify A).PosSemidef) : 0 ≤ mooreDifferential n A (OAI.Analysis.Calculus.Quaternion.outer v) :=
  mooreDifferential_nonneg_of_posSemidef A (OAI.Analysis.Calculus.Quaternion.outer v) hA (complexify_outer_posSemidef v)

end OAI.LinearAlgebra.Moore
