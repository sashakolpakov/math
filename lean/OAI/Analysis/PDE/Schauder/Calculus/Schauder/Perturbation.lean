import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Compact
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Interpolation

/-! The quantitative frozen-coefficient perturbation estimate. -/

noncomputable section
open _root_.MeasureTheory Set Metric InnerProductSpace Laplacian
namespace OAI.Analysis.PDE.Schauder

def nondivergenceOperator {m : ℕ}
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin m, A x i j * fderiv ℝ (fderiv ℝ u) x
    (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))

theorem laplacian_sub_nondivergenceOperator {m : ℕ}
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    laplacian u x - nondivergenceOperator A u x =
      ∑ i : Fin m, ∑ j : Fin m, ((if i = j then 1 else 0) - A x i j) *
        fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) := by
  simp only [sub_mul, Finset.sum_sub_distrib]
  simp [nondivergenceOperator, laplacian_coordinate]

theorem laplacian_perturbation_holder {m : ℕ}
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (u : EuclideanSpace ℝ (Fin m) → ℝ) {α θ M H K F : ℝ}
    (hθ : 0 ≤ θ) (hM : 0 ≤ M) (_ : 0 ≤ H) (_ : 0 ≤ K)
    (hclose : ∀ x i j, |(if i = j then 1 else 0) - A x i j| ≤ θ)
    (hA : ∀ x y i j, |A x i j - A y i j| ≤ M * ‖x - y‖ ^ α)
    (hDu : ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ K)
    (hHu : ∀ x y, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H * ‖x - y‖ ^ α)
    (hLu : ∀ x y, |nondivergenceOperator A u x - nondivergenceOperator A u y| ≤ F * ‖x - y‖ ^ α) :
    ∀ x y, |laplacian u x - laplacian u y| ≤
      (F + (m : ℝ) * m * (θ * H + M * K)) * ‖x - y‖ ^ α := by
  intro x y
  let D (x : EuclideanSpace ℝ (Fin m)) (i j : Fin m) :=
    fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))
  let R (x : EuclideanSpace ℝ (Fin m)) (i j : Fin m) := ((if i = j then 1 else 0) - A x i j) * D x i j
  have he (i j : Fin m) : |R x i j - R y i j| ≤ (θ * H + M * K) * ‖x - y‖ ^ α := by
    have hd := (euclidean_bilinear_entry_le_norm (fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y) i j).trans (hHu x y)
    have hy := (euclidean_bilinear_entry_le_norm (fderiv ℝ (fderiv ℝ u) y) i j).trans (hDu y)
    change |D x i j - D y i j| ≤ H * ‖x - y‖ ^ α at hd
    change |D y i j| ≤ K at hy
    have ha : |A y i j - A x i j| ≤ M * ‖x - y‖ ^ α := by simpa only [abs_sub_comm] using hA x y i j
    have hid : R x i j - R y i j =
        ((if i = j then 1 else 0) - A x i j) * (D x i j - D y i j) +
          (A y i j - A x i j) * D y i j := by dsimp [R]; ring
    calc
      _ ≤ |(if i = j then 1 else 0) - A x i j| * |D x i j - D y i j| +
          |A y i j - A x i j| * |D y i j| := by
        rw [hid]
        simpa only [abs_mul] using abs_add_le
          (((if i = j then 1 else 0) - A x i j) * (D x i j - D y i j))
          ((A y i j - A x i j) * D y i j)
      _ ≤ θ * (H * ‖x - y‖ ^ α) + (M * ‖x - y‖ ^ α) * K :=
        add_le_add (mul_le_mul (hclose x i j) hd (abs_nonneg _) hθ)
          (mul_le_mul ha hy (abs_nonneg _) (mul_nonneg hM (Real.rpow_nonneg (norm_nonneg _) _)))
      _ = _ := by ring
  have hres : |(laplacian u x - nondivergenceOperator A u x) -
      (laplacian u y - nondivergenceOperator A u y)| ≤
      (m : ℝ) * m * (θ * H + M * K) * ‖x - y‖ ^ α := by
    rw [laplacian_sub_nondivergenceOperator, laplacian_sub_nondivergenceOperator]
    change |(∑ i, ∑ j, R x i j) - (∑ i, ∑ j, R y i j)| ≤ _
    rw [← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i, ∑ j, |R x i j - R y i j| :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin m, ∑ _j : Fin m, (θ * H + M * K) * ‖x - y‖ ^ α :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => he i j
      _ = _ := by simp; ring
  have hid : laplacian u x - laplacian u y =
      (nondivergenceOperator A u x - nondivergenceOperator A u y) +
        ((laplacian u x - nondivergenceOperator A u x) - (laplacian u y - nondivergenceOperator A u y)) := by ring
  rw [hid]
  calc
    _ ≤ |nondivergenceOperator A u x - nondivergenceOperator A u y| +
        |(laplacian u x - nondivergenceOperator A u x) - (laplacian u y - nondivergenceOperator A u y)| := abs_add_le _ _
    _ ≤ F * ‖x - y‖ ^ α + (m : ℝ) * m * (θ * H + M * K) * ‖x - y‖ ^ α := add_le_add (hLu x y) hres
    _ = _ := by ring

end OAI.Analysis.PDE.Schauder
