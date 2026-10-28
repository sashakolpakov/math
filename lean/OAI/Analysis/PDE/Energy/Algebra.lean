import Mathlib

/-!
Algebraic components of Section 4 of `sections/energy.tex`.

These results formalize the determinant-segment integration and the Schur
inequality. They do not assert the PDE existence or integration-by-parts
theorems used to identify the coefficients of the energy.
-/

namespace OAI.Analysis.PDE.Energy

open _root_.MeasureTheory Matrix
open scoped MatrixOrder

/-- The two scalar coefficients of the rank-one determinant segment. -/
theorem integral_segment (n : ℕ) (X Y : ℝ) :
    (∫ t in (0 : ℝ)..1, t ^ (n + 1) * X + t ^ n * (1 - t) * Y) =
      X / (n + 2) + Y / ((n + 1) * (n + 2)) := by
  have h : (fun t : ℝ => t ^ (n + 1) * X + t ^ n * (1 - t) * Y) =
      (fun t => t ^ (n + 1) * X + (t ^ n * Y - t ^ (n + 1) * Y)) := by
    funext t
    rw [pow_succ]
    ring
  rw [h, intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_mul_const, integral_pow, integral_pow]
  · simp only [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero, Nat.cast_add,
      Nat.cast_one]
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have hn2 : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
    field_simp
    ring
  all_goals exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- The comparison step in Lemma `energy-comparison`, in dimension `n + 1`.
`Y ≤ (n+1) X` is the estimate furnished there by cofactor integration by parts. -/
theorem segment_energy_comparison (n : ℕ) {X Y : ℝ}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hYX : Y ≤ (n + 1) * X) :
    let E := -(∫ t in (0 : ℝ)..1, t ^ (n + 1) * X + t ^ n * (1 - t) * Y)
    (n : ℝ) / (n + 2) * X ≤ X + E ∧ X + E ≤ X := by
  dsimp only
  rw [integral_segment]
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hn2 : (0 : ℝ) < n + 2 := by positivity
  constructor
  · have hYdiv : Y / ((n + 1) * (n + 2)) ≤ X / (n + 2) := by
      apply (div_le_iff₀ (mul_pos hn1 hn2)).mpr
      calc
        Y ≤ (n + 1) * X := hYX
        _ = X / (n + 2) * ((n + 1) * (n + 2)) := by field_simp
    have hid : (n : ℝ) / (n + 2) * X = X - 2 * (X / (n + 2)) := by
      field_simp
      ring
    rw [hid]
    linarith
  · have : 0 ≤ X / (n + 2) + Y / ((n + 1) * (n + 2)) := by positivity
    linarith

section Matrices

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Positivity of the trace pairing of two real positive semidefinite matrices. -/
theorem trace_mul_nonneg {A B : Matrix n n ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  rw [star_eq_conjTranspose, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  exact (hA.mul_mul_conjTranspose_same C).trace_nonneg

/-- Removing the Schur complement from the time-time entry leaves a
positive semidefinite matrix, even when the original full matrix is indefinite. -/
theorem schur_remainder_posSemidef
    (B : Matrix Unit n ℝ) {D : Matrix n n ℝ} (hD : D.PosDef) [Invertible D] :
    (fromBlocks (B * D⁻¹ * Bᴴ) B Bᴴ D).PosSemidef := by
  rw [Matrix.PosDef.fromBlocks₂₂ _ _ hD, sub_self]
  exact Matrix.PosSemidef.zero

/-- The pointwise matrix inequality used in equation `schur-energy-inequality`,
for real symmetric matrices. The quaternionic extension is a separate task. -/
theorem schur_trace_lower_bound
    {A : Matrix (Unit ⊕ n) (Unit ⊕ n) ℝ} (hA : A.PosSemidef)
    (ℓ : ℝ) (B : Matrix Unit n ℝ) {D : Matrix n n ℝ}
    (hD : D.PosDef) [Invertible D] :
    A (Sum.inl ()) (Sum.inl ()) * (ℓ - (B * D⁻¹ * Bᴴ) () ()) ≤
      (A * fromBlocks (of fun _ _ : Unit => ℓ) B Bᴴ D).trace := by
  let s := ℓ - (B * D⁻¹ * Bᴴ) () ()
  let Q := fromBlocks (of fun _ _ : Unit => ℓ) B Bᴴ D
  let E : Matrix (Unit ⊕ n) (Unit ⊕ n) ℝ := single (Sum.inl ()) (Sum.inl ()) s
  have heq : Q - E = fromBlocks (B * D⁻¹ * Bᴴ) B Bᴴ D := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => simp [Q, E, s, fromBlocks, single]
      | inr j => simp [Q, E, fromBlocks, single]
    | inr i =>
      cases j with
      | inl j => simp [Q, E, fromBlocks, single]
      | inr j => simp [Q, E, fromBlocks, single]
  have hp := trace_mul_nonneg hA (schur_remainder_posSemidef B hD)
  rw [← heq, Matrix.mul_sub, trace_sub] at hp
  have htr : (A * E).trace = A (Sum.inl ()) (Sum.inl ()) * s := by
    simp [E, trace_mul_single]
  rw [htr] at hp
  exact sub_nonneg.mp hp

/-- Determinant form of the Schur complement, with the time block singled out. -/
theorem det_time_block (ℓ : ℝ) (B : Matrix Unit n ℝ)
    (D : Matrix n n ℝ) [Invertible D] :
    (fromBlocks (of fun _ _ : Unit => ℓ) B Bᴴ D).det =
      D.det * (ℓ - (B * D⁻¹ * Bᴴ) () ()) := by
  rw [det_fromBlocks₂₂, invOf_eq_nonsing_inv]
  congr 1
  rw [det_unique]
  rfl

/-- The normalized Schur energy inequality for real symmetric matrices.
The determinant constraint here is precisely the fiber equation's pointwise
algebraic constraint, not an assumption of the desired inequality. -/
theorem schur_energy_inequality
    {A : Matrix (Unit ⊕ n) (Unit ⊕ n) ℝ} (hA : A.PosSemidef)
    (ℓ : ℝ) (B : Matrix Unit n ℝ) {D : Matrix n n ℝ}
    (hD : D.PosDef) [Invertible D] {lam : ℝ} (hlam : lam ≠ 0)
    (hdet : D.det = lam * A (Sum.inl ()) (Sum.inl ())) :
    (fromBlocks (of fun _ _ : Unit => ℓ) B Bᴴ D).det / lam ≤
      (A * fromBlocks (of fun _ _ : Unit => ℓ) B Bᴴ D).trace := by
  rw [det_time_block, hdet]
  convert schur_trace_lower_bound hA ℓ B hD using 1
  field_simp

end Matrices

section RankOne

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Matrix determinant lemma, expressed with an outer product. -/
theorem det_add_outer {D : Matrix n n ℝ} (hD : D.det ≠ 0)
    (u v : n → ℝ) :
    (D + vecMulVec u v).det = D.det * (1 + v ⬝ᵥ (D⁻¹ *ᵥ u)) := by
  have hm : vecMulVec u v = replicateCol Unit u * replicateRow Unit v := by
    ext i j
    simp [Matrix.mul_apply, vecMulVec]
  rw [hm, det_add_replicateCol_mul_replicateRow (isUnit_iff_ne_zero.mpr hD)]
  congr 1
  rw [det_unique]
  simp only [Matrix.add_apply, Matrix.one_apply_eq]
  congr 1
  simp only [Matrix.mul_apply, replicateCol_apply, replicateRow_apply, dotProduct, mulVec,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  ext i
  congr 1
  ext j
  ring

/-- The rank-one determinant segment identity appearing in the proof of
Lemma `energy-comparison`, for real matrices of dimension at least two. -/
theorem det_rank_one_segment (k : ℕ)
    {D : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ} (hD : D.det ≠ 0)
    (u v : Fin (k + 2) → ℝ) (t : ℝ) :
    (t • D + (1 - t) • vecMulVec u v).det =
      t ^ (k + 2) * D.det +
        t ^ (k + 1) * (1 - t) * (D.det * (v ⬝ᵥ (D⁻¹ *ᵥ u))) := by
  by_cases ht : t = 0
  · subst t
    simp [det_vecMulVec]
  · have hscale : t • D + (1 - t) • vecMulVec u v =
        t • (D + vecMulVec (((1 - t) / t) • u) v) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply,
        Pi.smul_apply]
      field_simp
    rw [hscale, det_smul, det_add_outer hD, mulVec_smul, dotProduct_smul]
    simp only [Fintype.card_fin, smul_eq_mul]
    rw [pow_succ t (k + 1)]
    field_simp

/-- Exact integration of the determinant segment, now attached to actual
matrices rather than independent scalar coefficients. -/
theorem integral_det_rank_one_segment (k : ℕ)
    {D : Matrix (Fin (k + 2)) (Fin (k + 2)) ℝ} (hD : D.det ≠ 0)
    (u v : Fin (k + 2) → ℝ) :
    (∫ t in (0 : ℝ)..1, (t • D + (1 - t) • vecMulVec u v).det) =
      D.det / (k + 3) +
        (D.det * (v ⬝ᵥ (D⁻¹ *ᵥ u))) / ((k + 2) * (k + 3)) := by
  simp_rw [det_rank_one_segment k hD u v]
  convert integral_segment (k + 1) D.det (D.det * (v ⬝ᵥ (D⁻¹ *ᵥ u))) using 1
  push_cast
  ring

end RankOne

end OAI.Analysis.PDE.Energy
