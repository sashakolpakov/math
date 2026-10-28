import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CayleyCharacters

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Cayley
open scoped BigOperators

variable {r : ℕ}

theorem fourier_inversion_sum (f : Cube r → ℝ) (x : Cube r) :
    (∑ a, fourier f a * character a x) = (Fintype.card (Cube r) : ℝ) * f x := by
  classical
  simp only [fourier, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, character_orthogonal]
  simp [mul_comm]

theorem fourier_pairing (f g : Cube r → ℝ) :
    (∑ a, fourier f a * fourier g a) =
      (Fintype.card (Cube r) : ℝ) * ∑ x, f x * g x := by
  classical
  conv_lhs => arg 2; ext a; arg 2; unfold fourier
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ x, g x * ∑ a, fourier f a * character a x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by simp_rw [fourier_inversion_sum]; apply Finset.sum_congr rfl; intro x _; ring

theorem fourier_energy (f : Cube r → ℝ) :
    (∑ a, fourier f a ^ 2) = (Fintype.card (Cube r) : ℝ) * ∑ x, f x ^ 2 := by
  simpa only [pow_two] using fourier_pairing f f

noncomputable def adjacency {P : Type*} [Fintype P] (shifts : P → Cube r)
    (f : Cube r → ℝ) (x : Cube r) : ℝ := ∑ i, f (x + shifts i)

theorem sum_translate (f : Cube r → ℝ) (s : Cube r) :
    (∑ x, f (x + s)) = ∑ x, f x := by
  exact Fintype.sum_equiv (Equiv.addRight s) _ _ (fun _ => rfl)

theorem fourier_translate (f : Cube r → ℝ) (s a : Cube r) :
    fourier (fun x => f (x + s)) a = character a s * fourier f a := by
  classical
  have h := sum_translate (fun x => f (x + s) * character a x) s
  simp only [add_assoc, cube_add_self, add_zero, character_add_right] at h
  rw [fourier, ← h]
  unfold fourier
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem fourier_adjacency {P : Type*} [Fintype P] (shifts : P → Cube r)
    (f : Cube r → ℝ) (a : Cube r) :
    fourier (adjacency shifts f) a = walsh shifts a * fourier f a := by
  classical
  simp only [fourier, adjacency, Finset.sum_mul]
  rw [Finset.sum_comm]
  change (∑ i, fourier (fun x => f (x + shifts i)) a) = _
  simp_rw [fourier_translate]
  rw [← Finset.sum_mul]
  rfl

theorem adjacency_pairing {P : Type*} [Fintype P] (shifts : P → Cube r)
    (f g : Cube r → ℝ) :
    (Fintype.card (Cube r) : ℝ) * ∑ x, f x * adjacency shifts g x =
      ∑ a, walsh shifts a * (fourier f a * fourier g a) := by
  rw [← fourier_pairing]
  simp_rw [fourier_adjacency]
  apply Finset.sum_congr rfl
  intro a _
  ring


/-- Cauchy--Schwarz in the unnormalized Fourier coordinates. -/
theorem fourier_abs_pairing_le (f g : Cube r → ℝ) :
    (∑ a, |fourier f a| * |fourier g a|) ≤
      Real.sqrt ((Fintype.card (Cube r) : ℝ) * ∑ x, f x ^ 2) *
      Real.sqrt ((Fintype.card (Cube r) : ℝ) * ∑ x, g x ^ 2) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun a => |fourier f a|) (fun a => |fourier g a|)
  simpa only [sq_abs, fourier_energy] using h

/-- A spectral bound with an explicit constant-character term. -/
theorem adjacency_pairing_le {P : Type*} [Fintype P]
    (shifts : P → Cube r) (ε : ℝ) (hε : 0 ≤ ε) (hW : SmallWalsh shifts ε)
    (f g : Cube r → ℝ) :
    (Fintype.card (Cube r) : ℝ) * ∑ x, f x * adjacency shifts g x ≤
      (Fintype.card P : ℝ) * (∑ x, f x) * (∑ x, g x) +
      ε * Fintype.card P *
        (Real.sqrt ((Fintype.card (Cube r) : ℝ) * ∑ x, f x ^ 2) *
         Real.sqrt ((Fintype.card (Cube r) : ℝ) * ∑ x, g x ^ 2)) := by
  classical
  rw [adjacency_pairing]
  have hnonneg : 0 ≤ ε * (Fintype.card P : ℝ) := mul_nonneg hε (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ a : Cube r,
        ((if a = 0 then (Fintype.card P : ℝ) * fourier f 0 * fourier g 0 else 0) +
         ε * Fintype.card P * (|fourier f a| * |fourier g a|)) := by
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : a = 0
      · subst a
        simp only [walsh_zero, ite_true]
        have hp := mul_nonneg hnonneg (mul_nonneg (abs_nonneg (fourier f 0))
          (abs_nonneg (fourier g 0)))
        nlinarith
      · rw [ite_eq_right ha, zero_add]
        calc
          _ ≤ |walsh shifts a * (fourier f a * fourier g a)| := le_abs_self _
          _ = |walsh shifts a| * (|fourier f a| * |fourier g a|) := by rw [abs_mul, abs_mul]
          _ ≤ _ := mul_le_mul_of_nonneg_right (hW a ha)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (Fintype.card P : ℝ) * (∑ x, f x) * (∑ x, g x) +
        ε * Fintype.card P * (∑ a, |fourier f a| * |fourier g a|) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
    _ ≤ _ := add_le_add_right
      (mul_le_mul_of_nonneg_left (fourier_abs_pairing_le f g) hnonneg) _

theorem sqrt_scaled_product (N u v : ℝ) (hN : 0 ≤ N) (hu : 0 ≤ u) :
    Real.sqrt (N * u) * Real.sqrt (N * v) = N * Real.sqrt (u * v) := by
  rw [← Real.sqrt_mul (mul_nonneg hN hu),
    show N * u * (N * v) = N ^ 2 * (u * v) by ring,
    Real.sqrt_mul (sq_nonneg N), Real.sqrt_sq hN]

end SubexponentialSAT.SqrtLog.Cayley

end OAI.Algorithms
