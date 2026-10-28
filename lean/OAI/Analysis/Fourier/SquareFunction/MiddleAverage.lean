import OAI.Analysis.Fourier.SquareFunction.LocalizedL2

open OAI.Analysis.Fourier.Wave

/-! The middle-scale term on a cube, with the exact finite-window Holder
exponent. The global bound for its maximal envelope is in SteinVectorMaximal. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set Metric
open scoped ENNReal

theorem average_le_ballMaximal_of_volume_ratio {n : ℕ}
    (f : Space n → ℝ≥0∞) {Q : Set (Space n)}
    (hQ0 : volume Q ≠ 0) (hQtop : volume Q ≠ ∞)
    {c z : Space n} {R : ℝ} (hQball : Q ⊆ ball c R) (hz : z ∈ ball c R)
    {D : ℝ≥0∞} (hvol : volume (ball c R) ≤ D * volume Q) :
    (∫⁻ x in Q, f x) / volume Q ≤ D * ballMaximal volume f z := by
  have hb := euclidean_ball_finite_pos c (nonempty_ball.mp ⟨z, hz⟩)
  have havg : (∫⁻ x in ball c R, f x) ≤ ballMaximal volume f z * volume (ball c R) := by
    apply (ENNReal.div_le_iff_le_mul (.inl hb.1) (.inl hb.2)).mp
    exact le_iSup_of_le (c, R) (le_iSup_of_le hz le_rfl)
  apply (ENNReal.div_le_iff_le_mul (.inl hQ0) (.inl hQtop)).mpr
  calc
    _ ≤ ∫⁻ x in ball c R, f x := lintegral_mono' (Measure.restrict_mono_set _ hQball) le_rfl
    _ ≤ ballMaximal volume f z * volume (ball c R) := havg
    _ ≤ ballMaximal volume f z * (D * volume Q) := mul_le_mul_right hvol _
    _ = _ := by ac_rfl

/-- Local vector average bounded by the middle-scale maximal envelope. -/
theorem middle_vector_average {n : ℕ} {I H : Type*} [Fintype I]
    [NormedAddCommGroup H] [MeasurableSpace H] [BorelSpace H]
    (u : I → Space n → H) (hu : ∀ i, Measurable (u i))
    {Q : Set (Space n)} (hQ0 : volume Q ≠ 0) (hQtop : volume Q ≠ ∞)
    {c z : Space n} {R : ℝ} (hQball : Q ⊆ ball c R) (hz : z ∈ ball c R)
    {D : ℝ≥0∞} (hvol : volume (ball c R) ≤ D * volume Q)
    {p : ℝ} (hp : 2 ≤ p) :
    (∫⁻ x in Q, ENNReal.ofReal (vectorNorm (fun i => u i x))) / volume Q ≤
      (D ^ (1 / 2 : ℝ) * (Fintype.card I : ℝ≥0∞) ^ (1 / 2 - 1 / p)) *
        (∑ i, ballMaximal volume (fun x => ‖u i x‖ₑ ^ (2 : ℝ)) z ^ (p / 2)) ^ (1 / p) := by
  have hm : (∫⁻ x in Q, ENNReal.ofReal (vectorNorm (fun i => u i x)) ^ (2 : ℝ)) /
      volume Q ≤ D * ∑ i, ballMaximal volume (fun x => ‖u i x‖ₑ ^ (2 : ℝ)) z := by
    simp_rw [enorm_vectorNorm_sq]
    rw [lintegral_finsetSum Finset.univ (fun i _ => (hu i).enorm.pow_const 2),
      div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa only [div_eq_mul_inv] using average_le_ballMaximal_of_volume_ratio
      (fun x => ‖u i x‖ₑ ^ (2 : ℝ)) hQ0 hQtop hQball hz hvol
  calc
    _ ≤ ((∫⁻ x in Q, ENNReal.ofReal (vectorNorm (fun i => u i x)) ^ (2 : ℝ)) /
        volume Q) ^ (1 / 2 : ℝ) :=
      set_average_le_square_root volume _ (measurable_vectorNorm u hu).ennreal_ofReal Q hQ0 hQtop
    _ ≤ (D * ∑ i, ballMaximal volume (fun x => ‖u i x‖ₑ ^ (2 : ℝ)) z) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow hm (by positivity)
    _ = D ^ (1 / 2 : ℝ) * (∑ i, ballMaximal volume (fun x => ‖u i x‖ₑ ^ (2 : ℝ)) z) ^
        (1 / 2 : ℝ) := ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ ≤ D ^ (1 / 2 : ℝ) * ((Fintype.card I : ℝ≥0∞) ^ (1 / 2 - 1 / p) *
        (∑ i, ballMaximal volume (fun x => ‖u i x‖ₑ ^ (2 : ℝ)) z ^ (p / 2)) ^ (1 / p)) := by
      apply mul_le_mul_right
      simpa only [Finset.card_univ] using finite_middle_holder Finset.univ
        (fun i => ballMaximal volume (fun x => ‖u i x‖ₑ ^ (2 : ℝ)) z) hp
    _ = _ := (mul_assoc _ _ _).symm

theorem enorm_vectorNorm_mask_sq {I H : Type*} [Fintype I]
    [NormedAddCommGroup H] (v : I → H) (P : I → Prop) [DecidablePred P] :
    ENNReal.ofReal (vectorNorm (fun i => if P i then v i else 0)) ^ (2 : ℝ) =
      ∑ i ∈ Finset.univ.filter P, ‖v i‖ₑ ^ (2 : ℝ) := by
  rw [enorm_vectorNorm_sq, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : P i <;> simp [h]

/-- The middle-window estimate as a mask inside the original vector. Its
maximal envelope uses the full vector, whereas the cardinality factor uses
only the selected window. -/
theorem masked_middle_vector_average {n : ℕ} {I H : Type*} [Fintype I]
    [NormedAddCommGroup H] [MeasurableSpace H] [BorelSpace H]
    (u : I → Space n → H) (hu : ∀ i, Measurable (u i))
    (P : I → Prop) [DecidablePred P]
    {Q : Set (Space n)} (hQ0 : volume Q ≠ 0) (hQtop : volume Q ≠ ∞)
    {c z : Space n} {R : ℝ} (hQball : Q ⊆ ball c R) (hz : z ∈ ball c R)
    {D : ℝ≥0∞} (hvol : volume (ball c R) ≤ D * volume Q)
    {p : ℝ} (hp : 2 ≤ p) :
    (∫⁻ x in Q, ENNReal.ofReal (vectorNorm (fun i => if P i then u i x else 0))) / volume Q ≤
      (D ^ (1 / 2 : ℝ) * ((Finset.univ.filter P).card : ℝ≥0∞) ^ (1 / 2 - 1 / p)) *
        (∑ i, ballMaximal volume (fun x => ‖u i x‖ₑ ^ (2 : ℝ)) z ^ (p / 2)) ^ (1 / p) := by
  let s := Finset.univ.filter P
  have hum (i : I) : Measurable (fun x => if P i then u i x else 0) := by
    by_cases h : P i <;> simp only [h, ite_true, ite_false]
    · exact hu i
    · exact measurable_const
  have hm : (∫⁻ x in Q, ENNReal.ofReal (vectorNorm (fun i => if P i then u i x else 0)) ^ (2 : ℝ)) /
      volume Q ≤ D * ∑ i ∈ s, ballMaximal volume (fun x => ‖u i x‖ₑ ^ (2 : ℝ)) z := by
    simp_rw [enorm_vectorNorm_mask_sq]
    rw [lintegral_finsetSum s (fun i _ => (hu i).enorm.pow_const 2),
      div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa only [div_eq_mul_inv] using average_le_ballMaximal_of_volume_ratio
      (fun x => ‖u i x‖ₑ ^ (2 : ℝ)) hQ0 hQtop hQball hz hvol
  have hsum : (∑ i ∈ s, ballMaximal volume (fun x => ‖u i x‖ₑ ^ (2 : ℝ)) z ^ (p / 2)) ≤
      ∑ i, ballMaximal volume (fun x => ‖u i x‖ₑ ^ (2 : ℝ)) z ^ (p / 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => bot_le)
  calc
    _ ≤ ((∫⁻ x in Q, ENNReal.ofReal (vectorNorm (fun i => if P i then u i x else 0)) ^ (2 : ℝ)) /
        volume Q) ^ (1 / 2 : ℝ) :=
      set_average_le_square_root volume _ (measurable_vectorNorm _ hum).ennreal_ofReal Q hQ0 hQtop
    _ ≤ (D * ∑ i ∈ s, ballMaximal volume (fun x => ‖u i x‖ₑ ^ (2 : ℝ)) z) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow hm (by positivity)
    _ = D ^ (1 / 2 : ℝ) * (∑ i ∈ s, ballMaximal volume (fun x => ‖u i x‖ₑ ^ (2 : ℝ)) z) ^
        (1 / 2 : ℝ) := ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ ≤ D ^ (1 / 2 : ℝ) * ((s.card : ℝ≥0∞) ^ (1 / 2 - 1 / p) *
        (∑ i ∈ s, ballMaximal volume (fun x => ‖u i x‖ₑ ^ (2 : ℝ)) z ^ (p / 2)) ^ (1 / p)) :=
      mul_le_mul_right (finite_middle_holder s _ hp) _
    _ ≤ D ^ (1 / 2 : ℝ) * ((s.card : ℝ≥0∞) ^ (1 / 2 - 1 / p) *
        (∑ i, ballMaximal volume (fun x => ‖u i x‖ₑ ^ (2 : ℝ)) z ^ (p / 2)) ^ (1 / p)) :=
      mul_le_mul_right (mul_le_mul_right (ENNReal.rpow_le_rpow hsum (by positivity)) _) _
    _ = _ := (mul_assoc _ _ _).symm

end OAI.Analysis.Fourier.SquareFunction
