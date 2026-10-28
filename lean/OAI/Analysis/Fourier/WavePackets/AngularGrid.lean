import Mathlib

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set
open scoped ContDiff

/-- A smooth cardinal partition function, supported on `[-1,1]`.
Its translates telescope, so normalization introduces no scale-dependent
denominator. -/
def angularGridBump (x : ℝ) : ℝ :=
  Real.smoothTransition (x + 1) - Real.smoothTransition x

theorem contDiff_angularGridBump : ContDiff ℝ ∞ angularGridBump :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub
    Real.smoothTransition.contDiff

theorem angularGridBump_nonneg (x : ℝ) : 0 ≤ angularGridBump x := by
  exact sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith))

theorem angularGridBump_le_one (x : ℝ) : angularGridBump x ≤ 1 := by
  have := Real.smoothTransition.le_one (x + 1)
  have := Real.smoothTransition.nonneg x
  dsimp [angularGridBump]
  linarith

theorem angularGridBump_eq_zero {x : ℝ} (hx : x ≤ -1 ∨ 1 ≤ x) :
    angularGridBump x = 0 := by
  rcases hx with hx | hx
  · simp only [angularGridBump,
      Real.smoothTransition.zero_of_nonpos (show x + 1 ≤ 0 by linarith),
      Real.smoothTransition.zero_of_nonpos (show x ≤ 0 by linarith), sub_self]
  · simp only [angularGridBump,
      Real.smoothTransition.one_of_one_le (show 1 ≤ x + 1 by linarith),
      Real.smoothTransition.one_of_one_le hx, sub_self]

theorem angularGridBump_ne_zero {x : ℝ} (hx : angularGridBump x ≠ 0) :
    |x| < 1 := by
  by_contra hn
  have hn := le_of_not_gt hn
  exact hx (angularGridBump_eq_zero (by
    rcases le_abs.mp hn with h | h
    · exact Or.inr h
    · exact Or.inl (by linarith)))

theorem sum_angularGridBump_range (N : ℕ) (x : ℝ) :
    ∑ j ∈ Finset.range N, angularGridBump (x - j) =
      Real.smoothTransition (x + 1) - Real.smoothTransition (x - N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, angularGridBump]
    have he : x - (↑(N + 1) : ℝ) + 1 = x - N := by push_cast; ring
    rw [he]
    ring

/-- The finite interval of translates already sums to one throughout
`[-M,M]`. -/
theorem sum_angularGridBump_fin (M : ℕ) {x : ℝ} (hx : |x| ≤ M) :
    ∑ j : Fin (2 * M + 1), angularGridBump (x - ((j : ℕ) - (M : ℝ))) = 1 := by
  have he (j : ℕ) : x - (j - (M : ℝ)) = (x + M) - j := by ring
  simp_rw [he]
  rw [← Finset.sum_range (fun j : ℕ => angularGridBump (x + M - j)),
    sum_angularGridBump_range]
  have hlo : 1 ≤ x + M + 1 := by have := (abs_le.mp hx).1; linarith
  have hhi : x + M - (↑(2 * M + 1) : ℝ) + 1 ≤ 0 := by
    have := (abs_le.mp hx).2
    push_cast
    linarith
  rw [Real.smoothTransition.one_of_one_le hlo, Real.smoothTransition.zero_of_nonpos hhi]
  norm_num

/-- Tensor-product grid bump. We keep the coordinates as a finite real
product so that chart rescalings can be inserted by composition. -/
def angularGridProduct {d : ℕ} (x : Fin d → ℝ) : ℝ :=
  ∏ i, angularGridBump (x i)

theorem contDiff_angularGridProduct (d : ℕ) :
    ContDiff ℝ ∞ (angularGridProduct (d := d)) := by
  apply contDiff_prod
  intro i _
  exact contDiff_angularGridBump.comp (contDiff_apply ℝ ℝ i)

theorem angularGridProduct_nonneg {d : ℕ} (x : Fin d → ℝ) :
    0 ≤ angularGridProduct x := Finset.prod_nonneg (fun _ _ => angularGridBump_nonneg _)

theorem angularGridProduct_ne_zero {d : ℕ} {x : Fin d → ℝ}
    (hx : angularGridProduct x ≠ 0) (i : Fin d) : |x i| < 1 := by
  apply angularGridBump_ne_zero
  intro hz
  exact hx (Finset.prod_eq_zero (Finset.mem_univ i) hz)

theorem sum_angularGridProduct (d M : ℕ) {x : Fin d → ℝ}
    (hx : ∀ i, |x i| ≤ M) :
    ∑ k : Fin d → Fin (2 * M + 1),
      angularGridProduct (fun i => x i - ((k i : ℕ) - (M : ℝ))) = 1 := by
  unfold angularGridProduct
  dsimp only
  rw [← Fintype.prod_sum (fun i (j : Fin (2 * M + 1)) =>
    angularGridBump (x i - ((j : ℕ) - (M : ℝ))))]
  simp_rw [sum_angularGridBump_fin M (hx _)]
  simp

theorem tsupport_angularGridProduct_subset (d : ℕ) :
    tsupport (angularGridProduct (d := d)) ⊆ Set.Icc (fun _ => -1) (fun _ => 1) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  constructor <;> intro i
  · exact (abs_lt.mp (angularGridProduct_ne_zero hx i)).1.le
  · exact (abs_lt.mp (angularGridProduct_ne_zero hx i)).2.le

theorem hasCompactSupport_angularGridProduct (d : ℕ) :
    HasCompactSupport (angularGridProduct (d := d)) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_angularGridProduct_subset d)

def angularGridSize (R γ : ℝ) : ℕ := ⌈R / γ⌉₊

def angularGridCenter {d : ℕ} (R γ : ℝ)
    (k : Fin d → Fin (2 * angularGridSize R γ + 1)) (i : Fin d) : ℝ :=
  γ * ((k i : ℕ) - (angularGridSize R γ : ℝ))

/-- A grid in a fixed `d`-dimensional chart has the sharp `γ⁻ᵈ`
cardinality, including the endpoint and rounding costs. -/
theorem angularGrid_card_bound (d : ℕ) {R γ : ℝ} (hR : 0 ≤ R)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    (Fintype.card (Fin d → Fin (2 * angularGridSize R γ + 1)) : ℝ) ≤
      ((2 * R + 3) / γ) ^ d := by
  have hM := (Nat.ceil_lt_add_one (div_nonneg hR hγ.le)).le
  change (angularGridSize R γ : ℝ) ≤ R / γ + 1 at hM
  have hb : (2 * angularGridSize R γ + 1 : ℝ) ≤ (2 * R + 3) / γ := by
    apply (le_div_iff₀ hγ).mpr
    have hm := (mul_le_mul_of_nonneg_right hM hγ.le)
    rw [add_mul, div_mul_cancel₀ _ hγ.ne'] at hm
    nlinarith
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one]
  exact pow_le_pow_left₀ (by positivity) hb d

theorem angularGridCenter_bound {d : ℕ} {R γ : ℝ} (hR : 0 ≤ R)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (k : Fin d → Fin (2 * angularGridSize R γ + 1)) (i : Fin d) :
    |angularGridCenter R γ k i| ≤ R + 1 := by
  have hk : (k i : ℕ) ≤ 2 * angularGridSize R γ := Nat.le_of_lt_succ (k i).isLt
  have hk' : ((k i : ℕ) : ℝ) ≤ 2 * (angularGridSize R γ : ℝ) := by exact_mod_cast hk
  have hk0 : 0 ≤ ((k i : ℕ) : ℝ) := by positivity
  have hd : |((k i : ℕ) : ℝ) - angularGridSize R γ| ≤ angularGridSize R γ :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hM := (Nat.ceil_lt_add_one (div_nonneg hR hγ.le)).le
  change (angularGridSize R γ : ℝ) ≤ R / γ + 1 at hM
  have hm := mul_le_mul_of_nonneg_left hM hγ.le
  rw [mul_add, mul_div_cancel₀ _ hγ.ne', mul_one] at hm
  dsimp [angularGridCenter]
  rw [abs_mul, abs_of_pos hγ]
  exact (mul_le_mul_of_nonneg_left hd hγ.le).trans (by linarith)

theorem sum_scaled_angularGridProduct {d : ℕ} {R γ : ℝ} (hγ : 0 < γ)
    {x : Fin d → ℝ} (hx : ∀ i, |x i| ≤ R) :
    ∑ k : Fin d → Fin (2 * angularGridSize R γ + 1),
      angularGridProduct (fun i => (x i - angularGridCenter R γ k i) / γ) = 1 := by
  have he (k : Fin d → Fin (2 * angularGridSize R γ + 1)) (i : Fin d) :
      (x i - angularGridCenter R γ k i) / γ =
        x i / γ - ((k i : ℕ) - (angularGridSize R γ : ℝ)) := by
    dsimp [angularGridCenter]
    field_simp
  simp_rw [he]
  apply sum_angularGridProduct
  intro i
  rw [abs_div, abs_of_pos hγ]
  exact (div_le_div_of_nonneg_right (hx i) hγ.le).trans (Nat.le_ceil _)

end OAI.Analysis.Fourier.WavePackets
