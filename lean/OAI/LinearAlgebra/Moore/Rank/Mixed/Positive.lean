import OAI.LinearAlgebra.Moore.Rank.Mixed.Outer
import OAI.LinearAlgebra.MixedDiscriminant.Polarization
import OAI.LinearAlgebra.Moore.Rank.QuaternionDecomposition

noncomputable section

namespace OAI.LinearAlgebra.Moore

open Matrix OAI.Analysis.Calculus.Quaternion
open scoped ComplexOrder

/-- Inclusion-exclusion formula for the normalized Moore polarization. -/
theorem mixedMoore_polarization (m : ℕ)
    (A : Fin m → Matrix (Fin m) (Fin m) (Quaternion ℝ)) :
    (m.factorial : ℝ)⁻¹ *
        ∑ S : Finset (Fin m), (-1 : ℝ) ^ (m - S.card) * mooreDet m (∑ i ∈ S, A i) =
      mixedMoore m A := by
  simpa only [mixedMoore_const] using
    OAI.LinearAlgebra.MixedDiscriminant.symmetric_multilinear_polarization (mixedMoore m)
      (mixedMoore_comp_perm m) A

/-- On `m` quaternionic rank-one arguments the mixed determinant is exactly
the determinant of their sum divided by `m!`. -/
theorem mixedMoore_outer (m : ℕ) (v : Fin m → Fin m → Quaternion ℝ) :
    mixedMoore m (fun i => OAI.Analysis.Calculus.Quaternion.outer (v i)) =
      (m.factorial : ℝ)⁻¹ * mooreDet m (∑ i, OAI.Analysis.Calculus.Quaternion.outer (v i)) := by
  classical
  rw [← mixedMoore_polarization]
  congr 1
  rw [Finset.sum_eq_single Finset.univ]
  · simp
  · intro S hS hne
    rw [mooreDet_sum_outer_eq_zero_of_ne_univ v hne, mul_zero]
  · simp

theorem mixedMoore_outer_nonneg (m : ℕ) (v : Fin m → Fin m → Quaternion ℝ) :
    0 ≤ mixedMoore m (fun i => OAI.Analysis.Calculus.Quaternion.outer (v i)) := by
  rw [mixedMoore_outer]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (mooreDet_sum_outer_nonneg v)

/-- Positivity for genuine positive-semidefinite quaternionic arguments.
The finite rank-one decomposition is proved, not supplied as a premise. -/
theorem mixedMoore_nonneg {m : ℕ}
    (A : Fin m → Matrix (Fin m) (Fin m) (Quaternion ℝ))
    (hA : ∀ i, (complexify (A i)).PosSemidef) : 0 ≤ mixedMoore m A := by
  classical
  choose v hv using fun i => exists_sum_outer_of_complexify_posSemidef (A i) (hA i)
  have he : A = fun i => ∑ k, OAI.Analysis.Calculus.Quaternion.outer (v i k) := funext hv
  rw [he, (mixedMoore m).map_sum]
  exact Finset.sum_nonneg (fun f _ => mixedMoore_outer_nonneg m (fun i => v i (f i)))

end OAI.LinearAlgebra.Moore
