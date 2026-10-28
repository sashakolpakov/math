import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Decomposition
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.FarLipschitz

/-! The exponent-preserving Newtonian Schauder estimate for compact C² data.
The estimate is on the actual second Fréchet derivative, not a formal singular integral. -/

noncomputable section
open _root_.MeasureTheory Set Metric
namespace OAI.Analysis.PDE.Schauder

theorem schauder_scale_identity {r : ℝ} (hr : 0 < r) (α : ℝ) :
    (r / 2) ^ (α - 1) * r = (1 / 2 : ℝ) ^ (α - 1) * r ^ α := by
  rw [show r / 2 = (1 / 2 : ℝ) * r by ring,
    Real.mul_rpow (by positivity) hr.le, mul_assoc,
    ← Real.rpow_add_one hr.ne', sub_add_cancel]

theorem newtonianPotential_hessian_entry_holder {m : ℕ} (hm : 2 ≤ m)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (i j : Fin m) :
    ∃ C > 0, ∀ (f : EuclideanSpace ℝ (Fin m) → ℝ),
      ContDiff ℝ 2 f → HasCompactSupport f → ∀ H, 0 ≤ H →
      (∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) → ∀ x z,
      |fderiv ℝ (fderiv ℝ (newtonianPotential f)) z
          (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) -
        fderiv ℝ (fderiv ℝ (newtonianPotential f)) x
          (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))| ≤
        C * H * ‖z - x‖ ^ α := by
  let v : EuclideanSpace ℝ (Fin m) := EuclideanSpace.single i (1 : ℝ)
  let w : EuclideanSpace ℝ (Fin m) := EuclideanSpace.single j (1 : ℝ)
  obtain ⟨B, hB, hfar⟩ := farConvolution_difference_bound (show 1 ≤ m by omega) v w
  let N : ℝ := newtonianSizeConstant m *
    rieszBallMass (volume : Measure (EuclideanSpace ℝ (Fin m))) α * (3 : ℝ) ^ α
  let F : ℝ := B * (1 / 2 : ℝ) ^ (α - 1) *
    rieszTailMass (volume : Measure (EuclideanSpace ℝ (Fin m))) α
  let D : ℝ := if i = j then volume.real (ball (0 : EuclideanSpace ℝ (Fin m)) 1) * (2 - m) else 0
  have hN : 0 ≤ N := mul_nonneg (mul_nonneg (newtonianSizeConstant_nonneg m)
    (rieszBallMass_nonneg _ _)) (Real.rpow_nonneg (by norm_num) _)
  have hF : 0 ≤ F := mul_nonneg (mul_nonneg hB.le (Real.rpow_nonneg (by norm_num) _))
    (rieszTailMass_nonneg _ _)
  refine ⟨2 * N + F + |D| + 1, by positivity, ?_⟩
  intro f hf hfc H hH hh x z
  by_cases hxz : z = x
  · simp [hxz, Real.zero_rpow hα.ne']
  have hr : 0 < ‖z - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
  let r := ‖z - x‖
  have hinc (a : EuclideanSpace ℝ (Fin m)) : ∀ y, |f (a - y) - f a| ≤ H * ‖y‖ ^ α := by
    intro y
    have he : a - y - a = -y := by abel
    simpa only [he, norm_neg] using hh (a - y) a
  have hnear (a : EuclideanSpace ℝ (Fin m)) : |nearSingularPart f v w r a| ≤ N * H * r ^ α := by
    have hn := nearSingularPart_bound (show 1 ≤ m by omega) f a v w hr hH hα (hinc a)
    have hv : ‖v‖ = 1 := by simp [v]
    have hw : ‖w‖ = 1 := by simp [w]
    rw [hv, hw, mul_one, mul_one, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hr.le] at hn
    simpa only [N, mul_assoc, mul_comm, mul_left_comm] using hn
  have hfd : |scalarConvolution (truncatedNewtonianEntry m v w r) f z -
      scalarConvolution (truncatedNewtonianEntry m v w r) f x| ≤ F * H * r ^ α := by
    have ht := hfar r α H hr hα1 hH f (hf.of_le (by norm_num)) hfc hh x z
    have he : (H * B * (r / 2) ^ (α - 1) * rieszTailMass
        (volume : Measure (EuclideanSpace ℝ (Fin m))) α) * r = F * H * r ^ α := by
      calc
        _ = H * B * rieszTailMass (volume : Measure (EuclideanSpace ℝ (Fin m))) α *
            ((r / 2) ^ (α - 1) * r) := by ring
        _ = _ := by rw [schauder_scale_identity hr]; dsimp [F]; ring
    exact he ▸ ht
  have hd : |(f z - f x) * D| ≤ |D| * H * r ^ α := by
    rw [abs_mul]
    calc
      _ ≤ (H * r ^ α) * |D| := mul_le_mul_of_nonneg_right (hh z x) (abs_nonneg D)
      _ = _ := by ring
  change |fderiv ℝ (fderiv ℝ (newtonianPotential f)) z v w -
    fderiv ℝ (fderiv ℝ (newtonianPotential f)) x v w| ≤ _
  rw [newtonianPotential_hessian_near_far hm f hf hfc z i j hr,
    newtonianPotential_hessian_near_far hm f hf hfc x i j hr]
  change |nearSingularPart f v w r z + scalarConvolution (truncatedNewtonianEntry m v w r) f z + f z * D -
    (nearSingularPart f v w r x + scalarConvolution (truncatedNewtonianEntry m v w r) f x + f x * D)| ≤ _
  calc
    _ = |(nearSingularPart f v w r z - nearSingularPart f v w r x) +
        (scalarConvolution (truncatedNewtonianEntry m v w r) f z -
          scalarConvolution (truncatedNewtonianEntry m v w r) f x) + (f z - f x) * D| := by congr 1; ring
    _ ≤ (|nearSingularPart f v w r z| + |nearSingularPart f v w r x|) +
        |scalarConvolution (truncatedNewtonianEntry m v w r) f z -
          scalarConvolution (truncatedNewtonianEntry m v w r) f x| + |(f z - f x) * D| := by
      have h1 := abs_add_le
        (nearSingularPart f v w r z - nearSingularPart f v w r x +
          (scalarConvolution (truncatedNewtonianEntry m v w r) f z -
            scalarConvolution (truncatedNewtonianEntry m v w r) f x)) ((f z - f x) * D)
      have h2 := abs_add_le (nearSingularPart f v w r z - nearSingularPart f v w r x)
        (scalarConvolution (truncatedNewtonianEntry m v w r) f z -
          scalarConvolution (truncatedNewtonianEntry m v w r) f x)
      have h3 := abs_sub (nearSingularPart f v w r z) (nearSingularPart f v w r x)
      linarith only [h1, h2, h3]
    _ ≤ (2 * N + F + |D|) * H * r ^ α := by linarith [hnear z, hnear x]
    _ ≤ (2 * N + F + |D| + 1) * H * ‖z - x‖ ^ α := by
      dsimp [r]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hH)
        (Real.rpow_nonneg (norm_nonneg _) _)

end OAI.Analysis.PDE.Schauder
