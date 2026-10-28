import OAI.Analysis.PDE.Schauder.Calculus.Schauder.BallMoments

/-! The exact Hessian mass of a smooth radial regularization on a ball. -/

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped RealInnerProductSpace BigOperators
namespace OAI.Analysis.PDE.Schauder

theorem continuous_shiftedRadialHessian_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (p : ℝ) {s : ℝ} (hs : 0 < s) (v w : E) :
    Continuous (fun x => shiftedRadialHessian p s x v w) := by
  have h1 := (contDiff_shiftedRadialPower (E := E) (p - 1) hs).continuous
  have h2 := (contDiff_shiftedRadialPower (E := E) (p - 2) hs).continuous
  have he : (fun x => shiftedRadialHessian p s x v w) = fun x =>
      2 * p * shiftedRadialPower (p - 1) s x * ⟪v, w⟫ +
      4 * p * (p - 1) * shiftedRadialPower (p - 2) s x * ⟪x, v⟫ * ⟪x, w⟫ := by
    funext x
    exact shiftedRadialHessian_apply p s x v w
  rw [he]
  exact ((continuous_const.mul h1).mul continuous_const).add
    (((continuous_const.mul h2).mul (continuous_id.inner continuous_const)).mul
      (continuous_id.inner continuous_const))

theorem integrableOn_continuous_ball {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : Continuous f) (R : ℝ) : IntegrableOn f (ball 0 R) :=
  (hf.continuousOn.integrableOn_compact (isCompact_closedBall 0 R)).mono_set ball_subset_closedBall

theorem shiftedRadialHessian_coordinate {m : ℕ} (p s : ℝ) (i j : Fin m)
    (y : EuclideanSpace ℝ (Fin m)) :
    shiftedRadialHessian p s y (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) =
      2 * p * (s + ‖y‖ ^ 2) ^ (p - 1) * (if i = j then 1 else 0) +
      4 * p * (p - 1) * (s + ‖y‖ ^ 2) ^ (p - 2) * y i * y j := by
  rw [shiftedRadialHessian_apply]
  by_cases hij : i = j
  · subst j
    simp [EuclideanSpace.inner_single_right]
  · simp [EuclideanSpace.inner_single_right, hij, Ne.symm hij]

theorem shiftedRadialHessian_ball_diag_eq {m : ℕ} (p : ℝ) {s : ℝ} (hs : 0 < s)
    (R : ℝ) (i j : Fin m) :
    (∫ y in ball 0 R, shiftedRadialHessian p s y (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ))) =
    ∫ y in ball 0 R, shiftedRadialHessian p s y (EuclideanSpace.single j (1 : ℝ))
      (EuclideanSpace.single j (1 : ℝ)) := by
  have hA := integrableOn_continuous_ball
    (fun y : EuclideanSpace ℝ (Fin m) => 2 * p * (s + ‖y‖ ^ 2) ^ (p - 1))
    ((contDiff_shiftedRadialPower (p - 1) hs).continuous.const_mul _) R
  have hB (i : Fin m) := integrableOn_continuous_ball
    (fun y : EuclideanSpace ℝ (Fin m) => 4 * p * (p - 1) * (s + ‖y‖ ^ 2) ^ (p - 2) * y i * y i)
    ((((contDiff_shiftedRadialPower (p - 2) hs).continuous.const_mul _).mul
      (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i)).mul
        (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i)) R
  simp_rw [shiftedRadialHessian_coordinate, ite_true, mul_one]
  rw [integral_add hA (hB i), integral_add hA (hB j)]
  congr 1
  exact ballMoment_diagonal_eq (fun t => 4 * p * (p - 1) * (s + t ^ 2) ^ (p - 2)) R i j

theorem shiftedRadialHessian_ball_offDiagonal {m : ℕ} (p s R : ℝ) (i j : Fin m) (hij : i ≠ j) :
    (∫ y in ball 0 R, shiftedRadialHessian p s y (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single j (1 : ℝ))) = 0 := by
  simp_rw [shiftedRadialHessian_coordinate, ite_eq_right hij, mul_zero, zero_add]
  exact ballMoment_offDiagonal (fun t => 4 * p * (p - 1) * (s + t ^ 2) ^ (p - 2)) R i j hij

theorem shiftedRadialHessian_trace {m : ℕ} (p s : ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    (∑ i : Fin m, shiftedRadialHessian p s y (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ))) = radialTrace m p s ‖y‖ := by
  simp_rw [shiftedRadialHessian_coordinate, ite_true, mul_one]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have he : (∑ i : Fin m, 4 * p * (p - 1) * (s + ‖y‖ ^ 2) ^ (p - 2) * y i * y i) =
      4 * p * (p - 1) * (s + ‖y‖ ^ 2) ^ (p - 2) * ‖y‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [he]
  dsimp [radialTrace]
  ring

theorem shiftedRadialHessian_ball_mass {m : ℕ} (hm : 1 ≤ m) (p : ℝ) {s R : ℝ}
    (hs : 0 < s) (hR : 0 ≤ R) (i : Fin m) :
    (∫ y in ball 0 R, shiftedRadialHessian p s y (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ))) =
      volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) *
        (2 * p * R ^ m * (s + R ^ 2) ^ (p - 1)) := by
  apply mul_left_cancel₀ (show (m : ℝ) ≠ 0 by exact_mod_cast (show m ≠ 0 by omega))
  calc
    _ = ∑ j : Fin m, ∫ y in ball 0 R, shiftedRadialHessian p s y
        (EuclideanSpace.single j (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) := by
      simp_rw [shiftedRadialHessian_ball_diag_eq p hs R _ i]
      simp
    _ = ∫ y in ball 0 R, ∑ j : Fin m, shiftedRadialHessian p s y
        (EuclideanSpace.single j (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) := by
      exact (MeasureTheory.integral_finsetSum Finset.univ fun j _ =>
        integrableOn_continuous_ball _ (continuous_shiftedRadialHessian_apply p hs _ _) R).symm
    _ = ∫ y in ball (0 : EuclideanSpace ℝ (Fin m)) R, radialTrace m p s ‖y‖ := by
      simp only [shiftedRadialHessian_trace]
    _ = _ := by rw [integral_ball_radial hm, integral_radialTrace hm p hs hR]; ring

end OAI.Analysis.PDE.Schauder
