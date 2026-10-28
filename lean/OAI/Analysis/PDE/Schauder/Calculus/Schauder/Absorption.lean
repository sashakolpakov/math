import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Perturbation

/-! Absorption by iteration, and a uniform Schauder estimate near the identity matrix. -/

noncomputable section
open _root_.MeasureTheory Set Metric Filter InnerProductSpace Laplacian
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

theorem bound_of_half_improvement {X : Type*} (v w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    {B : ℝ} (hB : 0 ≤ B) (hfinite : ∃ H ≥ 0, ∀ x, v x ≤ H * w x)
    (himprove : ∀ H, 0 ≤ H → (∀ x, v x ≤ H * w x) → ∀ x, v x ≤ (H / 2 + B) * w x) :
    ∀ x, v x ≤ 2 * B * w x := by
  obtain ⟨H, hH, hbound⟩ := hfinite
  have hn (n : ℕ) : ∀ x, v x ≤ ((1 / 2 : ℝ) ^ n * H + 2 * B) * w x := by
    induction n with
    | zero =>
      intro x
      exact (hbound x).trans (mul_le_mul_of_nonneg_right (by simp only [pow_zero, one_mul]; linarith) (hw x))
    | succ n ih =>
      have h := himprove ((1 / 2 : ℝ) ^ n * H + 2 * B) (by positivity) ih
      intro x
      convert h x using 1 ; simp only [pow_succ] ; ring
  intro x
  have ht : Tendsto (fun n : ℕ => ((1 / 2 : ℝ) ^ n * H + 2 * B) * w x) atTop (𝓝 (2 * B * w x)) := by
    simpa using (((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_const H).add_const (2 * B)).mul_const (w x)
  exact ge_of_tendsto' ht (fun n => hn n x)

theorem near_identity_schauder {m : ℕ} (hm : 3 ≤ m) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ θ > 0, ∀ M, 0 ≤ M → ∃ C > 0,
      ∀ (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
        (u : EuclideanSpace ℝ (Fin m) → ℝ),
        ContDiff ℝ 2 u → HasCompactSupport u →
        (∀ x i j, |(if i = j then 1 else 0) - A x i j| ≤ θ) →
        (∀ x y i j, |A x i j - A y i j| ≤ M * ‖x - y‖ ^ α) →
        (∃ H ≥ 0, ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H * ‖x - y‖ ^ α) →
        ∀ F U, 0 ≤ F → 0 ≤ U → (∀ x, |u x| ≤ U) →
        (∀ x y, |nondivergenceOperator A u x - nondivergenceOperator A u y| ≤ F * ‖x - y‖ ^ α) →
        ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ C * (F + U) * ‖x - y‖ ^ α := by
  obtain ⟨S, hS, hschauder⟩ := compact_schauder_estimate_C2 hm hα hα1
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
    have hLp := laplacian_perturbation_holder A u hθ.le hM hH (by positivity : 0 ≤ ε * H + B * U)
      hclose hA hK hh hLu
    have hs := hschauder u hu huc (F + d * (θ * H + M * (ε * H + B * U))) (by positivity) hLp
    have hcoef : S * (F + d * (θ * H + M * (ε * H + B * U))) ≤ H / 2 + b := by
      have ha : S * d * (θ + M * ε) ≤ 1 / 2 := by nlinarith only [hθsmall, hεsmall]
      have ha' := mul_le_mul_of_nonneg_right ha hH
      dsimp [b]
      nlinarith only [ha']
    intro x y
    exact (hs y x).trans (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (norm_nonneg _) _))
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
