import Mathlib

/-! A quantitative gluing lemma: a boundary approach estimate together with
scale-invariant interior Hölder control gives ordinary Hölder control,
including pairs whose distance to the boundary tends to zero. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Metric

theorem holder_of_boundary_and_interior_bound
    {X Y : Type*} [MetricSpace X] [NormedAddCommGroup Y]
    {K : Set X} {f : X → Y} {height : X → ℝ}
    {a b κ A B C V : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hκ : 0 < κ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hV : 0 ≤ V)
    (hheight_nonneg : ∀ x ∈ K, 0 ≤ height x)
    (hbound : ∀ x ∈ K, ‖f x‖ ≤ V)
    (hboundary : ∀ x ∈ K, ∀ y ∈ K,
      ‖f x - f y‖ ≤ A * (height x + dist x y) ^ a + C * dist x y ^ a)
    (hinterior : ∀ x ∈ K, ∀ y ∈ K, 0 < height x →
      dist x y ≤ κ * height x / 2 →
      ‖f x - f y‖ ≤ B * (dist x y / height x) ^ b) :
    let γ := min a b / 2
    let q := min 1 ((κ / 2) ^ 2)
    let D := A * 2 ^ a + C + B + 2 * V / q ^ γ + 1
    ∀ x ∈ K, ∀ y ∈ K, ‖f x - f y‖ ≤ D * dist x y ^ γ := by
  let γ := min a b / 2
  let q := min 1 ((κ / 2) ^ 2)
  have hγ : 0 < γ := half_pos (lt_min ha hb)
  have hq : 0 < q := lt_min zero_lt_one (sq_pos_of_pos (half_pos hκ))
  have hqpow : 0 < q ^ γ := Real.rpow_pos_of_pos hq _
  let D := A * 2 ^ a + C + B + 2 * V / q ^ γ + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hterm : 0 ≤ 2 * V / q ^ γ := by positivity
  have htermA : 0 ≤ A * 2 ^ a := by positivity
  change ∀ x ∈ K, ∀ y ∈ K, ‖f x - f y‖ ≤ D * dist x y ^ γ
  intro x hx y hy
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, norm_zero, dist_self]
    positivity
  have hd : 0 < dist x y := dist_pos.mpr hxy
  let d := dist x y
  have hd' : 0 < d := hd
  by_cases hsmall : d < q
  · have hd1 : d ≤ 1 := hsmall.le.trans (min_le_left _ _)
    have hdκ : d ≤ (κ / 2) ^ 2 := hsmall.le.trans (min_le_right _ _)
    have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 hd'
    have hs2 : (Real.sqrt d) ^ 2 = d := Real.sq_sqrt hd'.le
    have hs1 : Real.sqrt d ≤ 1 := by nlinarith
    have hds : d ≤ Real.sqrt d := by nlinarith
    have hsκ : Real.sqrt d ≤ κ / 2 := by nlinarith
    have hpowa : d ^ (a / 2) ≤ d ^ γ :=
      Real.rpow_le_rpow_of_exponent_ge' hd'.le hd1 hγ.le
        (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
    have hpowb : d ^ (b / 2) ≤ d ^ γ :=
      Real.rpow_le_rpow_of_exponent_ge' hd'.le hd1 hγ.le
        (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
    have hsa : (Real.sqrt d) ^ a = d ^ (a / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hd'.le]
      congr 1
      ring
    have hsb : (Real.sqrt d) ^ b = d ^ (b / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hd'.le]
      congr 1
      ring
    by_cases hheight : height x ≤ Real.sqrt d
    · have hbase : height x + d ≤ 2 * Real.sqrt d := by linarith
      have hpow : (height x + d) ^ a ≤ (2 * Real.sqrt d) ^ a := by
        exact Real.rpow_le_rpow (add_nonneg (hheight_nonneg x hx) hd'.le) hbase ha.le
      have hpa : d ^ a ≤ d ^ (a / 2) :=
        Real.rpow_le_rpow_of_exponent_ge' hd'.le hd1 (half_pos ha).le (by linarith)
      have hrough := hboundary x hx y hy
      have ht : ‖f x - f y‖ ≤ (A * 2 ^ a + C) * d ^ (a / 2) := by
        calc
          ‖f x - f y‖ ≤ A * (height x + d) ^ a + C * d ^ a := hrough
          _ ≤ A * (2 * Real.sqrt d) ^ a + C * d ^ (a / 2) :=
            add_le_add (mul_le_mul_of_nonneg_left hpow hA) (mul_le_mul_of_nonneg_left hpa hC)
          _ = (A * 2 ^ a + C) * d ^ (a / 2) := by
            rw [Real.mul_rpow (by norm_num) hs.le, hsa]
            ring
      calc
        ‖f x - f y‖ ≤ (A * 2 ^ a + C) * d ^ (a / 2) := ht
        _ ≤ (A * 2 ^ a + C) * d ^ γ := mul_le_mul_of_nonneg_left hpowa (by positivity)
        _ ≤ D * d ^ γ := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hd'.le _)
          dsimp [D]
          linarith
    · have hh : Real.sqrt d < height x := lt_of_not_ge hheight
      have hhpos : 0 < height x := hs.trans hh
      have hclose : d ≤ κ * height x / 2 := by nlinarith
      have hratio : d / height x ≤ Real.sqrt d := by
        apply (div_le_iff₀ hhpos).2
        nlinarith
      have hpow := Real.rpow_le_rpow (div_pos hd' hhpos).le hratio hb.le
      rw [hsb] at hpow
      calc
        ‖f x - f y‖ ≤ B * (d / height x) ^ b := hinterior x hx y hy hhpos hclose
        _ ≤ B * d ^ (b / 2) := mul_le_mul_of_nonneg_left hpow hB
        _ ≤ B * d ^ γ := mul_le_mul_of_nonneg_left hpowb hB
        _ ≤ D * d ^ γ := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hd'.le _)
          dsimp [D]
          linarith
  · have hlarge : q ≤ d := le_of_not_gt hsmall
    have hpow : q ^ γ ≤ d ^ γ := Real.rpow_le_rpow hq.le hlarge hγ.le
    calc
      ‖f x - f y‖ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
      _ ≤ 2 * V := by linarith [hbound x hx, hbound y hy]
      _ = (2 * V / q ^ γ) * q ^ γ := by field_simp
      _ ≤ (2 * V / q ^ γ) * d ^ γ := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ D * d ^ γ := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hd'.le _)
        dsimp [D]
        linarith

end OAI.Analysis.PDE.Elliptic
