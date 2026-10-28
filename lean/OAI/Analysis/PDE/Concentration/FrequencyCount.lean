import OAI.Analysis.PDE.Concentration.SpatialCellL2

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set OAI.Analysis.Calculus.Current

/-- A finite set of distinct integer frequency vectors in a cube has the
expected polynomial cardinality, uniformly in the semiclassical scale. -/
theorem integer_frequency_count {ι J : Type*} [Fintype ι] [Fintype J]
    (m : ι → J → ℤ) (hm : Function.Injective m) {B h : ℝ}
    (hB : 0 ≤ B) (hh : 0 < h) (hh1 : h ≤ 1)
    (hbound : ∀ i j, |(m i j : ℝ)| ≤ B / h) :
    (Fintype.card ι : ℝ) * h ^ Fintype.card J ≤ (2 * B + 3) ^ Fintype.card J := by
  classical
  let N : ℕ := ⌈B / h⌉₊
  have hN (i : ι) (j : J) : -(N : ℤ) ≤ m i j ∧ m i j ≤ N := by
    have hb : |(m i j : ℝ)| ≤ (N : ℝ) := (hbound i j).trans (Nat.le_ceil _)
    obtain ⟨hl, hu⟩ := abs_le.mp hb
    constructor
    · exact_mod_cast hl
    · exact_mod_cast hu
  let enc : ι → J → Fin (2 * N + 1) := fun i j =>
    ⟨(m i j + (N : ℤ)).toNat, by have := hN i j; omega⟩
  have he : Function.Injective enc := by
    intro i k hik
    apply hm
    funext j
    have hhij := congrArg (fun f : J → Fin (2 * N + 1) => (f j).val) hik
    dsimp only [enc] at hhij
    have hi := hN i j
    have hk := hN k j
    omega
  have hc : Fintype.card ι ≤ (2 * N + 1) ^ Fintype.card J := by
    simpa only [Fintype.card_fun, Fintype.card_fin] using Fintype.card_le_of_injective enc he
  have hceil : (N : ℝ) ≤ B / h + 1 := (Nat.ceil_lt_add_one (div_nonneg hB hh.le)).le
  have hscalar : ((2 * N + 1 : ℕ) : ℝ) * h ≤ 2 * B + 3 := by
    have hmul := mul_le_mul_of_nonneg_right hceil hh.le
    have hdiv : B / h * h = B := div_mul_cancel₀ B hh.ne'
    push_cast
    nlinarith
  calc
    _ ≤ (((2 * N + 1 : ℕ) : ℝ) ^ Fintype.card J) * h ^ Fintype.card J :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (pow_nonneg hh.le _)
    _ = ((((2 * N + 1 : ℕ) : ℝ) * h) ^ Fintype.card J) := (mul_pow _ _ _).symm
    _ ≤ _ := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hh.le) hscalar _

theorem finiteWave_norm_sq_le_card {d : ℕ} {ι : Type*} [Fintype ι]
    (ξ : ι → OAI.Analysis.Calculus.Current.SpatialSpace d) (a : ι → ℂ) (x : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    ‖finiteWave ξ a x‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖a i‖ ^ 2 := by
  have h := norm_finiteWave_le ξ a x
  have hs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖a i‖)
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans (by simpa only [Finset.card_univ] using hs)

/-- Supremum normalization forces nontrivial Fourier energy; this form keeps
the finite frequency count explicit and does not require a supremum to be
attained. -/
theorem finiteWave_energy_lower {d : ℕ} {ι : Type*} [Fintype ι]
    (ξ : ι → OAI.Analysis.Calculus.Current.SpatialSpace d) (a : ι → ℂ) {h C : ℝ} (hh : 0 < h)
    (hcount : (Fintype.card ι : ℝ) * h ^ (d + 1) ≤ C)
    (hnorm : ∀ b < (1 : ℝ), ∃ x, b < ‖finiteWave ξ a x‖ ^ 2) :
    h ^ (d + 1) ≤ C * ∑ i, ‖a i‖ ^ 2 := by
  have hs : 1 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖a i‖ ^ 2 := by
    by_contra hc
    obtain ⟨x, hx⟩ := hnorm _ (lt_of_not_ge hc)
    exact (not_lt_of_ge (finiteWave_norm_sq_le_card ξ a x)) hx
  have hsum : 0 ≤ ∑ i, ‖a i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h1 := mul_le_mul_of_nonneg_right hs (pow_nonneg hh.le (d + 1))
  have h2 := mul_le_mul_of_nonneg_right hcount hsum
  nlinarith

end OAI.Analysis.PDE.Concentration
