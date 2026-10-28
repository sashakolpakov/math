import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Normalization
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Absorption

/-! Freezing at an arbitrary positive definite real matrix, rather than only the identity. -/

noncomputable section
open _root_.MeasureTheory Set Metric Filter InnerProductSpace Laplacian
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

theorem constant_operator_sub {m : ℕ}
    (A₀ : Matrix (Fin m) (Fin m) ℝ)
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    nondivergenceOperator (fun _ => A₀) u x - nondivergenceOperator A u x =
      ∑ i : Fin m, ∑ j : Fin m, (A₀ i j - A x i j) *
        fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) := by
  simp only [sub_mul, Finset.sum_sub_distrib, nondivergenceOperator]

theorem constant_operator_perturbation_holder {m : ℕ}
    (A₀ : Matrix (Fin m) (Fin m) ℝ)
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (u : EuclideanSpace ℝ (Fin m) → ℝ) {α θ M H K F : ℝ}
    (hθ : 0 ≤ θ) (hM : 0 ≤ M)
    (hclose : ∀ x i j, |A₀ i j - A x i j| ≤ θ)
    (hA : ∀ x y i j, |A x i j - A y i j| ≤ M * ‖x - y‖ ^ α)
    (hDu : ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ K)
    (hHu : ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H * ‖x - y‖ ^ α)
    (hLu : ∀ x y, |nondivergenceOperator A u x - nondivergenceOperator A u y| ≤ F * ‖x - y‖ ^ α) :
    ∀ x y, |nondivergenceOperator (fun _ => A₀) u x - nondivergenceOperator (fun _ => A₀) u y| ≤
      (F + (m : ℝ) * m * (θ * H + M * K)) * ‖x - y‖ ^ α := by
  intro x y
  let D (x : EuclideanSpace ℝ (Fin m)) (i j : Fin m) :=
    fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))
  let R (x : EuclideanSpace ℝ (Fin m)) (i j : Fin m) := (A₀ i j - A x i j) * D x i j
  have he (i j : Fin m) : |R x i j - R y i j| ≤ (θ * H + M * K) * ‖x - y‖ ^ α := by
    have hd := (euclidean_bilinear_entry_le_norm (fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y) i j).trans (hHu x y)
    have hy := (euclidean_bilinear_entry_le_norm (fderiv ℝ (fderiv ℝ u) y) i j).trans (hDu y)
    change |D x i j - D y i j| ≤ H * ‖x - y‖ ^ α at hd
    change |D y i j| ≤ K at hy
    have ha : |A y i j - A x i j| ≤ M * ‖x - y‖ ^ α := by simpa only [abs_sub_comm] using hA x y i j
    have hid : R x i j - R y i j =
        (A₀ i j - A x i j) * (D x i j - D y i j) +
          (A y i j - A x i j) * D y i j := by dsimp [R]; ring
    calc
      _ ≤ |A₀ i j - A x i j| * |D x i j - D y i j| +
          |A y i j - A x i j| * |D y i j| := by
        rw [hid]
        simpa only [abs_mul] using abs_add_le
          ((A₀ i j - A x i j) * (D x i j - D y i j)) ((A y i j - A x i j) * D y i j)
      _ ≤ θ * (H * ‖x - y‖ ^ α) + (M * ‖x - y‖ ^ α) * K :=
        add_le_add (mul_le_mul (hclose x i j) hd (abs_nonneg _) hθ)
          (mul_le_mul ha hy (abs_nonneg _) (mul_nonneg hM (Real.rpow_nonneg (norm_nonneg _) _)))
      _ = _ := by ring
  have hres : |(nondivergenceOperator (fun _ => A₀) u x - nondivergenceOperator A u x) -
      (nondivergenceOperator (fun _ => A₀) u y - nondivergenceOperator A u y)| ≤
      (m : ℝ) * m * (θ * H + M * K) * ‖x - y‖ ^ α := by
    rw [constant_operator_sub, constant_operator_sub]
    change |(∑ i, ∑ j, R x i j) - (∑ i, ∑ j, R y i j)| ≤ _
    rw [← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i, ∑ j, |R x i j - R y i j| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin m, ∑ _j : Fin m, (θ * H + M * K) * ‖x - y‖ ^ α :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => he i j
      _ = _ := by simp; ring
  have hid : nondivergenceOperator (fun _ => A₀) u x - nondivergenceOperator (fun _ => A₀) u y =
      (nondivergenceOperator A u x - nondivergenceOperator A u y) +
        ((nondivergenceOperator (fun _ => A₀) u x - nondivergenceOperator A u x) -
          (nondivergenceOperator (fun _ => A₀) u y - nondivergenceOperator A u y)) := by ring
  rw [hid]
  calc
    _ ≤ |nondivergenceOperator A u x - nondivergenceOperator A u y| +
        |(nondivergenceOperator (fun _ => A₀) u x - nondivergenceOperator A u x) -
          (nondivergenceOperator (fun _ => A₀) u y - nondivergenceOperator A u y)| := abs_add_le _ _
    _ ≤ F * ‖x - y‖ ^ α + (m : ℝ) * m * (θ * H + M * K) * ‖x - y‖ ^ α := add_le_add (hLu x y) hres
    _ = _ := by ring

theorem frozen_coefficient_schauder {m : ℕ} (hm : 3 ≤ m) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (A₀ : Matrix (Fin m) (Fin m) ℝ) (hA₀ : A₀.PosDef) :
    ∃ θ > 0, ∀ M, 0 ≤ M → ∃ C > 0,
      ∀ (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
        (u : EuclideanSpace ℝ (Fin m) → ℝ),
        ContDiff ℝ 2 u → HasCompactSupport u →
        (∀ x i j, |A₀ i j - A x i j| ≤ θ) →
        (∀ x y i j, |A x i j - A y i j| ≤ M * ‖x - y‖ ^ α) →
        (∃ H ≥ 0, ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H * ‖x - y‖ ^ α) →
        ∀ F U, 0 ≤ F → 0 ≤ U → (∀ x, |u x| ≤ U) →
        (∀ x y, |nondivergenceOperator A u x - nondivergenceOperator A u y| ≤ F * ‖x - y‖ ^ α) →
        ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ C * (F + U) * ‖x - y‖ ^ α := by
  obtain ⟨S, hS, hschauder⟩ := compact_posDef_schauder hm hα hα1 A₀ hA₀
  let d : ℝ := (m : ℝ) * m
  have hd : 0 ≤ d := by positivity
  obtain ⟨θ, hθ, hθsmall⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1 / 4) (S * d)
  refine ⟨θ, hθ, ?_⟩
  intro M hM
  obtain ⟨ε, hε, hεsmall⟩ := exists_pos_mul_lt (by norm_num : (0 : ℝ) < 1 / 4) (S * d * M)
  obtain ⟨B, hB, hinterp⟩ := hessian_interpolation (m := m) hα hε
  let C : ℝ := 2 * S * (1 + d * M * B) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro A u hu huc hclose hA hfinite F U hF hU hub hLu
  let b : ℝ := S * (F + d * M * B * U)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have himprove (H : ℝ) (hH : 0 ≤ H)
      (hh : ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H * ‖x - y‖ ^ α) :
      ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ (H / 2 + b) * ‖x - y‖ ^ α := by
    have hK := hinterp u hu huc H U hH hU hub hh
    have hLp := constant_operator_perturbation_holder A₀ A u hθ.le hM hclose hA hK hh hLu
    have hs := hschauder u hu huc (F + d * (θ * H + M * (ε * H + B * U))) (by positivity) hLp
    have hcoef : S * (F + d * (θ * H + M * (ε * H + B * U))) ≤ H / 2 + b := by
      have ha : S * d * (θ + M * ε) ≤ 1 / 2 := by nlinarith only [hθsmall, hεsmall]
      have ha' := mul_le_mul_of_nonneg_right ha hH
      dsimp [b]
      nlinarith only [ha']
    intro x y
    exact (hs x y).trans (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (norm_nonneg _) _))
  have hfinal := bound_of_half_improvement
    (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) =>
      ‖fderiv ℝ (fderiv ℝ u) p.1 - fderiv ℝ (fderiv ℝ u) p.2‖)
    (fun p => ‖p.1 - p.2‖ ^ α) (fun _ => Real.rpow_nonneg (norm_nonneg _) _) hb
    (by obtain ⟨H, hH, hh⟩ := hfinite; exact ⟨H, hH, fun p => hh p.1 p.2⟩)
    (fun H hH hh p => himprove H hH (fun x y => hh (x,y)) p.1 p.2)
  have hconstant : 2 * b ≤ C * (F + U) := by
    have hprod : 0 ≤ d * M * B := by positivity
    dsimp [b, C]
    nlinarith only [hprod, hS.le, hF, hU, mul_nonneg hprod hF, mul_nonneg hS.le hU,
      mul_nonneg hS.le (mul_nonneg hprod hF)]
  intro x y
  exact (hfinal (x,y)).trans (mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg (norm_nonneg _) _))

end OAI.Analysis.PDE.Schauder
