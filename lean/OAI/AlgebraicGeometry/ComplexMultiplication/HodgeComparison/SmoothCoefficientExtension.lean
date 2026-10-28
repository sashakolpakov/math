import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Elliptic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue

/-! # Smooth Coefficient Extension -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothCoefficientExtension.CM.Construction

noncomputable section

/-! Smooth localization of positive metric coefficients by a genuine cutoff.
The extension is constant off a compact set, hence bounded and Lipschitz. -/

open Set
open scoped ContDiff _root_.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def smoothCoefficientExtension (η : E → ℝ) (A : E → F →L[ℝ] F) (x : E) : F →L[ℝ] F :=
  ContinuousLinearMap.id ℝ F + η x • (A x - ContinuousLinearMap.id ℝ F)

omit [NormedSpace ℝ E] in
theorem smoothCoefficientExtension_eq_identity (η : E → ℝ) (A : E → F →L[ℝ] F)
    {x : E} (hx : x ∉ tsupport η) :
    smoothCoefficientExtension η A x = ContinuousLinearMap.id ℝ F := by
  rw [smoothCoefficientExtension, image_eq_zero_of_notMem_tsupport hx, zero_smul, add_zero]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem smoothCoefficientExtension_eq_coefficient (η : E → ℝ) (A : E → F →L[ℝ] F)
    {x : E} (hx : η x = 1) : smoothCoefficientExtension η A x = A x := by
  rw [smoothCoefficientExtension, hx, one_smul]
  abel

theorem smoothCoefficientExtension_smooth (η : E → ℝ) (A : E → F →L[ℝ] F)
    {U : Set E} (hU : IsOpen U) (hη : ContDiff ℝ ∞ η) (hηU : tsupport η ⊆ U)
    (hA : ContDiffOn ℝ ∞ A U) : ContDiff ℝ ∞ (smoothCoefficientExtension η A) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact contDiffAt_const.add (hη.contDiffAt.smul ((hA.contDiffAt (hU.mem_nhds hx)).sub contDiffAt_const))
  · have hzero : η =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hηU h))
    have heq : smoothCoefficientExtension η A =ᶠ[𝓝 x] (fun _ => ContinuousLinearMap.id ℝ F) := by
      filter_upwards [hzero] with y hy
      simp only [smoothCoefficientExtension, hy, Pi.zero_apply, zero_smul, add_zero]
    exact contDiffAt_const.congr_of_eventuallyEq heq

omit [NormedSpace ℝ E] in
theorem smoothCoefficientExtension_compact_perturbation (η : E → ℝ) (A : E → F →L[ℝ] F)
    (hη : HasCompactSupport η) :
    HasCompactSupport (fun x => smoothCoefficientExtension η A x - ContinuousLinearMap.id ℝ F) := by
  apply hη.mono'
  intro x hx
  by_contra hn
  exact hx (by
    change smoothCoefficientExtension η A x - ContinuousLinearMap.id ℝ F = 0
    rw [smoothCoefficientExtension_eq_identity η A hn, sub_self])

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem smoothCoefficientExtension_inner (η : E → ℝ) (A : E → F →L[ℝ] F) (x : E) (w : F) :
    inner ℝ (smoothCoefficientExtension η A x w) w =
      (1 - η x) * (‖w‖ * ‖w‖) + η x * inner ℝ (A x w) w := by
  simp only [smoothCoefficientExtension, add_apply, smul_apply, sub_apply,
    ContinuousLinearMap.id_apply, inner_add_left, real_inner_smul_left, inner_sub_left,
    real_inner_self_eq_norm_sq]
  ring

omit [NormedSpace ℝ E] in
theorem smoothCoefficientExtension_lower_bound (η : E → ℝ) (A : E → F →L[ℝ] F)
    (hη₀ : ∀ x, 0 ≤ η x) (hη₁ : ∀ x, η x ≤ 1) {a : ℝ}
    (hA : ∀ x ∈ tsupport η, ∀ w : F, a * ‖w‖ * ‖w‖ ≤ inner ℝ (A x w) w)
    (x : E) (w : F) :
    min a 1 * ‖w‖ * ‖w‖ ≤ inner ℝ (smoothCoefficientExtension η A x w) w := by
  by_cases hx : x ∈ tsupport η
  · rw [smoothCoefficientExtension_inner]
    let q := ‖w‖ * ‖w‖
    have hq : 0 ≤ q := mul_self_nonneg _
    have hma := mul_le_mul_of_nonneg_right (min_le_left a 1) hq
    have hm1 : min a 1 * q ≤ q := by
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right (min_le_right a 1) hq)
    have hpos : a * q ≤ inner ℝ (A x w) w := by simpa only [q, mul_assoc] using hA x hx w
    change min a 1 * ‖w‖ * ‖w‖ ≤ (1 - η x) * q + η x * inner ℝ (A x w) w
    calc
      _ = (1 - η x) * (min a 1 * q) + η x * (min a 1 * q) := by dsimp [q]; ring
      _ ≤ (1 - η x) * q + η x * (a * q) :=
        add_le_add (mul_le_mul_of_nonneg_left hm1 (sub_nonneg.mpr (hη₁ x)))
          (mul_le_mul_of_nonneg_left hma (hη₀ x))
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hpos (hη₀ x))
  · rw [smoothCoefficientExtension_eq_identity η A hx, ContinuousLinearMap.id_apply,
      real_inner_self_eq_norm_sq]
    have h := mul_le_mul_of_nonneg_right (min_le_right a 1) (mul_self_nonneg ‖w‖)
    simpa only [one_mul, pow_two, mul_assoc] using h

theorem smoothCoefficientExtension_bounded (η : E → ℝ) (A : E → F →L[ℝ] F)
    (hsmooth : ContDiff ℝ ∞ (smoothCoefficientExtension η A)) (hη : HasCompactSupport η) :
    ∃ C : ℝ, ∀ x, ‖smoothCoefficientExtension η A x‖ ≤ C := by
  let P := fun x => smoothCoefficientExtension η A x - ContinuousLinearMap.id ℝ F
  have hPc : HasCompactSupport P := smoothCoefficientExtension_compact_perturbation η A hη
  obtain ⟨C, hC⟩ := hPc.exists_bound_of_continuous (hsmooth.continuous.sub continuous_const)
  refine ⟨‖ContinuousLinearMap.id ℝ F‖ + C, fun x => ?_⟩
  calc
    _ = ‖ContinuousLinearMap.id ℝ F + P x‖ := by congr 1; dsimp [P]; abel
    _ ≤ ‖ContinuousLinearMap.id ℝ F‖ + ‖P x‖ := norm_add_le _ _
    _ ≤ _ := add_le_add le_rfl (hC x)

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] in
theorem compact_smooth_lipschitz {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (P : E → G) (hP : ContDiff ℝ ∞ P) (hPc : HasCompactSupport P) :
    ∃ L : NNReal, LipschitzWith L P := by
  have hD : Continuous (fderiv ℝ P) := hP.continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ := (hPc.fderiv ℝ).exists_bound_of_continuous hD
  let L : NNReal := ⟨max C 0, le_max_right _ _⟩
  refine ⟨L, lipschitzWith_of_nnnorm_fderiv_le (hP.differentiable (by simp)) ?_⟩
  intro x
  apply NNReal.coe_le_coe.mp
  exact (hC x).trans (le_max_left _ _)

theorem smoothCoefficientExtension_lipschitz (η : E → ℝ) (A : E → F →L[ℝ] F)
    (hsmooth : ContDiff ℝ ∞ (smoothCoefficientExtension η A)) (hη : HasCompactSupport η) :
    ∃ L : NNReal, LipschitzWith L (smoothCoefficientExtension η A) := by
  let P := fun x => smoothCoefficientExtension η A x - ContinuousLinearMap.id ℝ F
  have hP : ContDiff ℝ ∞ P := hsmooth.sub contDiff_const
  have hPc : HasCompactSupport P := smoothCoefficientExtension_compact_perturbation η A hη
  obtain ⟨L, hLip⟩ := compact_smooth_lipschitz P hP hPc
  refine ⟨L, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
  have h := hLip.dist_le_mul x y
  simpa only [dist_eq_norm, P, sub_sub_sub_cancel_right] using h

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothCoefficientExtension.CM.Construction
