import OAI.Analysis.PDE.Schauder.Calculus.Schauder.HolderSolution
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.PoissonSharp

/-! An actual C²,α right inverse of the Laplacian on compact C^α data. -/

noncomputable section
open _root_.MeasureTheory Set Metric Filter InnerProductSpace Laplacian
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

theorem laplacian_newtonianPotential_holder {m : ℕ} (hm : 2 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    {H α : ℝ} (hH : 0 ≤ H) (hα : 0 < α) (hα1 : α < 1)
    (hh : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α)
    (x : EuclideanSpace ℝ (Fin m)) :
    laplacian (newtonianPotential f) x = poissonNormalization m * f x := by
  have hJ := (newtonianPotential_C2_limit hm f hf hfc hH hα hα1 hh).2.2
  have ht : Tendsto (fun k => laplacian (mollifiedNewtonianPotential f k) x) atTop
      (𝓝 (laplacian (newtonianPotential f) x)) := by
    simp only [laplacian_coordinate]
    apply tendsto_finsetSum
    intro i _
    exact clm_apply_tendsto (clm_apply_tendsto (hJ.tendsto_at x) (EuclideanSpace.single i 1)) (EuclideanSpace.single i 1)
  have he (k : ℕ) : laplacian (mollifiedNewtonianPotential f k) x =
      poissonNormalization m * smoothData (standardMollifier m k) f x :=
    laplacian_newtonianPotential hm _ ((contDiff_smoothData _ f hf).of_le (by simp))
      (hasCompactSupport_smoothData _ f hfc) x
  simp only [he] at ht
  exact tendsto_nhds_unique ht ((smoothData_tendsto f hf x).const_mul (poissonNormalization m))

theorem contDiff_poissonPotential_holder {m : ℕ} (hm : 2 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    {H α : ℝ} (hH : 0 ≤ H) (hα : 0 < α) (hα1 : α < 1)
    (hh : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) :
    ContDiff ℝ 2 (poissonPotential f) := by
  simpa only [poissonPotential, Pi.smul_apply] using!
    (newtonianPotential_C2_limit hm f hf hfc hH hα hα1 hh).1.const_smul (poissonNormalization m)⁻¹

theorem laplacian_poissonPotential_holder {m : ℕ} (hm : 3 ≤ m)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    {H α : ℝ} (hH : 0 ≤ H) (hα : 0 < α) (hα1 : α < 1)
    (hh : ∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α)
    (x : EuclideanSpace ℝ (Fin m)) : laplacian (poissonPotential f) x = f x := by
  have hu := (newtonianPotential_C2_limit (show 2 ≤ m by omega) f hf hfc hH hα hα1 hh).1
  rw [poissonPotential, laplacian_smul _ hu.contDiffAt,
    laplacian_newtonianPotential_holder (show 2 ≤ m by omega) f hf hfc hH hα hα1 hh x]
  change (poissonNormalization m)⁻¹ * (poissonNormalization m * f x) = f x
  rw [← mul_assoc, inv_mul_cancel₀ (poissonNormalization_ne_zero hm), one_mul]

theorem poissonPotential_holder_hessian {m : ℕ} (hm : 3 ≤ m)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C > 0, ∀ (f : EuclideanSpace ℝ (Fin m) → ℝ),
      Continuous f → HasCompactSupport f → ∀ H, 0 ≤ H →
      (∀ x y, |f x - f y| ≤ H * ‖x - y‖ ^ α) → ∀ x z,
      ‖fderiv ℝ (fderiv ℝ (poissonPotential f)) z -
        fderiv ℝ (fderiv ℝ (poissonPotential f)) x‖ ≤ C * H * ‖z - x‖ ^ α := by
  obtain ⟨C, hC, hb⟩ := newtonianPotential_holder_hessian (show 2 ≤ m by omega) hα hα1
  have hn : 0 < |(poissonNormalization m)⁻¹| := abs_pos.mpr (inv_ne_zero (poissonNormalization_ne_zero hm))
  refine ⟨|(poissonNormalization m)⁻¹| * C, mul_pos hn hC, ?_⟩
  intro f hf hfc H hH hh x z
  have hu := (newtonianPotential_C2_limit (show 2 ≤ m by omega) f hf hfc hH hα hα1 hh).1
  simp only [poissonPotential, second_fderiv_const_smul _ hu]
  have h := mul_le_mul_of_nonneg_left (hb f hf hfc H hH hh z x) hn.le
  have hs (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) :
      ‖(poissonNormalization m)⁻¹ • A‖ ≤ |(poissonNormalization m)⁻¹| * ‖A‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    change ‖(poissonNormalization m)⁻¹ * A v w‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs]
    calc
      _ ≤ |(poissonNormalization m)⁻¹| * (‖A v‖ * ‖w‖) :=
        mul_le_mul_of_nonneg_left ((A v).le_opNorm w) (abs_nonneg _)
      _ ≤ |(poissonNormalization m)⁻¹| * ((‖A‖ * ‖v‖) * ‖w‖) := by
        gcongr
        exact A.le_opNorm v
      _ = _ := by ring
  have hsub (A B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) :
      (poissonNormalization m)⁻¹ • A - (poissonNormalization m)⁻¹ • B =
        (poissonNormalization m)⁻¹ • (A - B) := by
    ext v w
    change (poissonNormalization m)⁻¹ * A v w - (poissonNormalization m)⁻¹ * B v w =
      (poissonNormalization m)⁻¹ * (A v w - B v w)
    ring
  rw [hsub]
  exact (hs _).trans (by simpa only [mul_assoc] using h)

end OAI.Analysis.PDE.Schauder
