import OAI.Analysis.Fourier.SquareFunction.ScaleSums

/-! Sharp dyadic summation for Fourier transforms of endpoint power singularities.
The two positive exponents describe the low-frequency size and the excess
high-frequency decay of a smooth dyadic piece. -/

open scoped BigOperators

namespace OAI.Analysis.Fourier.Radial

theorem dyadic_rpow_comm (k : ℤ) (a : ℝ) :
    ((2 : ℝ) ^ k) ^ a = ((2 : ℝ) ^ a) ^ k := by
  exact (Real.rpow_zpow_comm (by norm_num : (0 : ℝ) ≤ 2) a k).symm

theorem dyadic_rpow_reverse (k j : ℤ) (a : ℝ) :
    ((2 : ℝ) ^ (k - j)) ^ a = ((2 : ℝ) ^ (-a)) ^ (j - k) := by
  rw [dyadic_rpow_comm, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_zpow,
    ← zpow_neg]
  congr 1
  omega

theorem finite_dyadic_min_sum {a b r : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hr : 0 < r) (s : Finset ℤ) :
    ∑ k ∈ s, min (((2 : ℝ) ^ k * r) ^ a) (((2 : ℝ) ^ k * r) ^ (-b)) ≤
      (1 - (2 : ℝ) ^ (-a))⁻¹ +
        (2 : ℝ) ^ b * (1 - (2 : ℝ) ^ (-b))⁻¹ := by
  classical
  obtain ⟨j, hjlo, hjhi⟩ := OAI.Analysis.Fourier.SquareFunction.exists_dyadic_reference hr
  have hta : (2 : ℝ) ^ (-a) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have htb : (2 : ℝ) ^ (-b) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hlo : ∑ k ∈ s.filter (· ≤ j),
      min (((2 : ℝ) ^ k * r) ^ a) (((2 : ℝ) ^ k * r) ^ (-b)) ≤
      (1 - (2 : ℝ) ^ (-a))⁻¹ := by
    calc
      _ ≤ ∑ k ∈ s.filter (· ≤ j), ((2 : ℝ) ^ (-a)) ^ (j - k) := by
        apply Finset.sum_le_sum
        intro k hk
        apply (min_le_left _ _).trans
        rw [← dyadic_rpow_reverse]
        exact Real.rpow_le_rpow (by positivity) (OAI.Analysis.Fourier.SquareFunction.reference_scale_upper hjhi k) ha.le
      _ ≤ _ := OAI.Analysis.Fourier.SquareFunction.finite_geometric_lower (by positivity) hta (by
        intro k hk
        exact (Finset.mem_filter.mp hk).2)
  have hhi : ∑ k ∈ s.filter (fun k => ¬k ≤ j),
      min (((2 : ℝ) ^ k * r) ^ a) (((2 : ℝ) ^ k * r) ^ (-b)) ≤
      (2 : ℝ) ^ b * (1 - (2 : ℝ) ^ (-b))⁻¹ := by
    calc
      _ ≤ ∑ k ∈ s.filter (fun k => ¬k ≤ j),
          (2 : ℝ) ^ b * ((2 : ℝ) ^ (-b)) ^ (k - j) := by
        apply Finset.sum_le_sum
        intro k hk
        apply (min_le_right _ _).trans
        have he : (2 : ℝ) ^ (k - j) / 2 ≤ (2 : ℝ) ^ k * r := by
          rw [OAI.Analysis.Fourier.SquareFunction.dyadic_scale_identity k j r]
          nlinarith [zpow_pos (by norm_num : (0 : ℝ) < 2) (k - j)]
        calc
          _ ≤ ((2 : ℝ) ^ (k - j) / 2) ^ (-b) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) he (by linarith)
          _ = _ := by
            rw [Real.div_rpow (by positivity) (by norm_num), dyadic_rpow_comm,
              Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
            ring
      _ = (2 : ℝ) ^ b * ∑ k ∈ s.filter (fun k => ¬k ≤ j),
          ((2 : ℝ) ^ (-b)) ^ (k - j) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (OAI.Analysis.Fourier.SquareFunction.finite_geometric_upper (by positivity) htb (by
          intro k hk
          have := (Finset.mem_filter.mp hk).2
          omega)) (by positivity)
  have he := Finset.sum_filter_add_sum_filter_not s (fun k => k ≤ j)
    (fun k => min (((2 : ℝ) ^ k * r) ^ a) (((2 : ℝ) ^ k * r) ^ (-b)))
  linarith

theorem endpoint_decay_le_min {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) :
    x ^ a * (1 + x) ^ (-(a + b)) ≤ min (x ^ a) (x ^ (-b)) := by
  apply le_min
  · have h : (1 + x) ^ (-(a + b)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    nlinarith [Real.rpow_pos_of_pos hx a]
  · calc
      _ ≤ x ^ a * x ^ (-(a + b)) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hx (by linarith) (by linarith)) (by positivity)
      _ = x ^ (-b) := by rw [← Real.rpow_add hx]; congr 1; ring

theorem finite_dyadic_endpoint_decay {a b r : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hr : 0 < r) (s : Finset ℤ) :
    ∑ k ∈ s, ((2 : ℝ) ^ k) ^ a * (1 + (2 : ℝ) ^ k * r) ^ (-(a + b)) ≤
      r ^ (-a) * ((1 - (2 : ℝ) ^ (-a))⁻¹ +
        (2 : ℝ) ^ b * (1 - (2 : ℝ) ^ (-b))⁻¹) := by
  calc
    _ ≤ ∑ k ∈ s, r ^ (-a) *
        min (((2 : ℝ) ^ k * r) ^ a) (((2 : ℝ) ^ k * r) ^ (-b)) := by
      apply Finset.sum_le_sum
      intro k hk
      have he : ((2 : ℝ) ^ k) ^ a = r ^ (-a) * ((2 : ℝ) ^ k * r) ^ a := by
        rw [Real.mul_rpow (by positivity) hr.le, Real.rpow_neg hr.le]
        field_simp
      rw [he, mul_assoc]
      exact mul_le_mul_of_nonneg_left (endpoint_decay_le_min ha hb (by positivity)) (by positivity)
    _ = r ^ (-a) * ∑ k ∈ s,
        min (((2 : ℝ) ^ k * r) ^ a) (((2 : ℝ) ^ k * r) ^ (-b)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (finite_dyadic_min_sum ha hb hr s) (by positivity)

theorem norm_endpoint_sum_le {a b r C : ℝ} {f : ℕ → ℂ} {z : ℂ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (hC : 0 ≤ C)
    (hf : HasSum f z)
    (hbound : ∀ j, ‖f j‖ ≤ C * ((2 : ℝ) ^ (-(j : ℤ))) ^ a *
      (1 + (2 : ℝ) ^ (-(j : ℤ)) * r) ^ (-(a + b))) :
    ‖z‖ ≤ C * r ^ (-a) * ((1 - (2 : ℝ) ^ (-a))⁻¹ +
      (2 : ℝ) ^ b * (1 - (2 : ℝ) ^ (-b))⁻¹) := by
  classical
  apply le_of_tendsto hf.tendsto_sum_nat.norm
  apply Filter.Eventually.of_forall
  intro N
  have hi : Function.Injective (fun j : ℕ => -(j : ℤ)) := by
    intro j k h
    exact_mod_cast neg_injective h
  have H := finite_dyadic_endpoint_decay ha hb hr
    ((Finset.range N).image (fun j : ℕ => -(j : ℤ)))
  rw [Finset.sum_image (fun _ _ _ _ h => hi h)] at H
  calc
    ‖∑ j ∈ Finset.range N, f j‖ ≤ ∑ j ∈ Finset.range N, ‖f j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range N, C * (((2 : ℝ) ^ (-(j : ℤ))) ^ a *
        (1 + (2 : ℝ) ^ (-(j : ℤ)) * r) ^ (-(a + b))) := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [mul_assoc] using hbound j
    _ = C * ∑ j ∈ Finset.range N, (((2 : ℝ) ^ (-(j : ℤ))) ^ a *
        (1 + (2 : ℝ) ^ (-(j : ℤ)) * r) ^ (-(a + b))) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left H hC

end OAI.Analysis.Fourier.Radial
