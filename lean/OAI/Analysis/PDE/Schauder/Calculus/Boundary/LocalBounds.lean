import OAI.Analysis.PDE.Schauder.Calculus.Boundary.ScaledEquiv
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.JetTransform
import OAI.Analysis.PDE.Schauder.Dirichlet.HalfspaceLowerInterpolation

/-! Uniform local lower-jet estimates in boundary-normalized coordinates. -/

noncomputable section
open Set Metric Filter
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

theorem norm_fderiv_le_affine {m : ℕ}
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 2 u)
    (L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (x₀ x : EuclideanSpace ℝ (Fin m)) :
    ‖fderiv ℝ u x‖ ≤
      ‖fderiv ℝ (fun z => u (x₀ + L z)) (L.symm (x-x₀))‖ * ‖L.symm.toContinuousLinearMap‖ := by
  have he : (fderiv ℝ (fun z => u (x₀ + L z)) (L.symm (x-x₀))).comp L.symm.toContinuousLinearMap =
      fderiv ℝ u x := by
    have hd := OAI.Analysis.PDE.Nonlinear.fderiv_linearAffine u (hu.differentiable (by norm_num))
      x₀ (L.symm (x-x₀)) L.toContinuousLinearMap
    change fderiv ℝ (fun z => u (x₀ + L z)) (L.symm (x-x₀)) = _ at hd
    rw [hd]
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      L.apply_symm_apply, add_sub_cancel]
  rw [← he]
  exact ContinuousLinearMap.opNorm_comp_le _ _

theorem norm_second_fderiv_le_affine {m : ℕ}
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 2 u)
    (L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (x₀ x : EuclideanSpace ℝ (Fin m)) :
    ‖fderiv ℝ (fderiv ℝ u) x‖ ≤
      ‖fderiv ℝ (fderiv ℝ (fun z => u (x₀ + L z))) (L.symm (x-x₀))‖ * ‖L.symm.toContinuousLinearMap‖^2 := by
  apply bilinear_norm_le_pullback
  intro v w
  have hd := second_fderiv_comp_affine u hu L.toContinuousLinearMap x₀
    (L.symm (x-x₀)) (L.symm v) (L.symm w)
  simpa only [ContinuousLinearEquiv.coe_coe, L.apply_symm_apply, add_sub_cancel] using hd.symm

theorem fderiv_radialCutoff_mul_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u : E → ℝ) {r : ℝ} (hr : 0 < r) (x : E) (hx : ‖x‖ < r) :
    fderiv ℝ (fun y => radialCutoff r y * u y) x = fderiv ℝ u x := by
  apply Filter.EventuallyEq.fderiv_eq
  have hb : ∀ᶠ y in 𝓝 x, y ∈ ball 0 r := isOpen_ball.mem_nhds (by simpa using hx)
  filter_upwards [hb] with y hy
  rw [radialCutoff_one hr (le_of_lt (by simpa only [mem_ball, dist_zero_right] using hy)), one_mul]

theorem affine_halfspace_local_lower_jets {m : ℕ} (k : Fin m) {α J ε : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hJ : 0 ≤ J) (hε : 0 < ε) :
    ∃ D > 0, ∀ (L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)),
      ‖L.symm.toContinuousLinearMap‖ ≤ J → ∀ c : ℝ, 0 < c →
      (∀ z, L z k = c * z k) →
      ∀ (x₀ : EuclideanSpace ℝ (Fin m)), x₀ k = 0 →
      ∀ (u : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ 2 u →
      ∀ H M, 0 ≤ H → 0 ≤ M →
      (∀ z, 0 ≤ z k → |radialCutoff (1/2) z * u (x₀ + L z)| ≤ M) →
      (∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
        ‖fderiv ℝ (fderiv ℝ (fun z => radialCutoff (1/2) z * u (x₀ + L z))) x -
          fderiv ℝ (fderiv ℝ (fun z => radialCutoff (1/2) z * u (x₀ + L z))) y‖ ≤ H * ‖x-y‖^α) →
      ∀ x ∈ ball x₀ ((1/4)/(J+1)), 0 ≤ x k →
        |u x| ≤ M ∧ ‖fderiv ℝ u x‖ ≤ ε*H+D*M ∧ ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ ε*H+D*M := by
  let C := J^2+J+1
  have hC : 0 < C := by dsimp only [C]; positivity
  obtain ⟨B, hB, hb⟩ := halfspace_lower_jet_interpolation k hα hα1 (div_pos hε hC)
  refine ⟨C*B, by positivity, ?_⟩
  intro L hLn c hc hnormal x₀ hx₀ u hu H M hH hM hbound hh x hx hxk
  let v := fun z => u (x₀ + L z)
  let w := fun z => radialCutoff (1/2) z * v z
  have hv : ContDiff ℝ 2 v := hu.comp (contDiff_const.add L.contDiff)
  have hw : ContDiff ℝ 2 w := ((contDiff_radialCutoff _).of_le (by simp)).mul hv
  have hwc : HasCompactSupport w := (hasCompactSupport_radialCutoff (by norm_num)).mul_right
  obtain ⟨hess, grad, _, _⟩ := hb w hw hwc H M hH hM hbound hh
  let z := L.symm (x-x₀)
  have hpoint : x₀ + L z = x := by simp only [z, L.apply_symm_apply, add_sub_cancel]
  have hzk : 0 ≤ z k := by
    have he := hnormal z
    have he' : c * z k = x k := by
      rw [← he]
      simp only [z, L.apply_symm_apply, PiLp.sub_apply, hx₀, sub_zero]
    exact nonneg_of_mul_nonneg_right (by rw [he']; exact hxk) hc
  have hznorm : ‖z‖ < 1/4 := by
    have hxx : ‖x-x₀‖ < (1/4)/(J+1) := by simpa only [mem_ball, dist_eq_norm] using hx
    calc
      _ ≤ ‖L.symm.toContinuousLinearMap‖ * ‖x-x₀‖ := L.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ J * ‖x-x₀‖ := mul_le_mul_of_nonneg_right hLn (norm_nonneg _)
      _ ≤ (J+1) * ‖x-x₀‖ := by nlinarith [norm_nonneg (x-x₀)]
      _ < (J+1) * ((1/4)/(J+1)) := mul_lt_mul_of_pos_left hxx (by positivity)
      _ = 1/4 := by field_simp
  have hzh : ‖z‖ < 1/2 := by linarith
  have hvalue : w z = u x := by
    change radialCutoff (1/2) z * u (x₀ + L z) = _
    rw [radialCutoff_one (by norm_num) hzh.le, one_mul, hpoint]
  have hg := grad z hzk
  have h2 := hess z hzk
  rw [fderiv_radialCutoff_mul_eq v (by norm_num) z hzh] at hg
  rw [hessian_radialCutoff_mul_eq v (by norm_num) z hzh] at h2
  let A := (ε/C)*H+B*M
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hCJ : J ≤ C := by dsimp only [C]; nlinarith [sq_nonneg J]
  have hCJ2 : J^2 ≤ C := by dsimp only [C]; linarith
  have hCA : C*A = ε*H+(C*B)*M := by dsimp only [A]; field_simp
  refine ⟨?_, ?_, ?_⟩
  · have hvb := hbound z hzk
    change |w z| ≤ M at hvb
    rwa [hvalue] at hvb
  · calc
      _ ≤ ‖fderiv ℝ v z‖ * ‖L.symm.toContinuousLinearMap‖ := norm_fderiv_le_affine u hu L x₀ x
      _ ≤ A * C := mul_le_mul hg (hLn.trans hCJ) (norm_nonneg _) hA
      _ = _ := by rw [mul_comm, hCA]
  · calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ v) z‖ * ‖L.symm.toContinuousLinearMap‖^2 := norm_second_fderiv_le_affine u hu L x₀ x
      _ ≤ A * C := mul_le_mul h2 ((pow_le_pow_left₀ (norm_nonneg _) hLn 2).trans hCJ2) (sq_nonneg _) hA
      _ = _ := by rw [mul_comm, hCA]

end OAI.Analysis.PDE.Schauder
