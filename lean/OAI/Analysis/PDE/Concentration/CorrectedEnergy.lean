import OAI.Analysis.PDE.Concentration.LocalLaplacian
import OAI.Analysis.PDE.Concentration.Supermean

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory InnerProductSpace Laplacian Set
open scoped ContDiff

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem laplacian_euclidean_coordinate_square (i : ι) (x : EuclideanSpace ℝ ι) :
    Δ (fun y : EuclideanSpace ℝ ι => (y i) ^ 2) x = 2 := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun ι ℝ)]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  change (∑ j : ι, (fderiv ℝ (fderiv ℝ (fun y => (y i) ^ 2)) x
    ((EuclideanSpace.basisFun ι ℝ) j)) ((EuclideanSpace.basisFun ι ℝ) j)) = 2
  have hh (v w : EuclideanSpace ℝ ι) :
      (fderiv ℝ (fderiv ℝ (fun y => (y i) ^ 2)) x v) w = 2 * v i * w i :=
    hessian_linear_square (EuclideanSpace.proj i) x v w
  simp_rw [hh]
  simp [EuclideanSpace.basisFun_apply, PiLp.single_apply]

def coordinateCylinderCorrection (i j : ι) (z : EuclideanSpace ℝ ι) : ℝ :=
  16 - (z i) ^ 2 - (z j) ^ 2

omit [DecidableEq ι] in
theorem contDiff_coordinateCylinderCorrection (i j : ι) :
    ContDiff ℝ 2 (coordinateCylinderCorrection i j) := by
  unfold coordinateCylinderCorrection
  fun_prop

theorem laplacian_coordinateCylinderCorrection (i j : ι) (z : EuclideanSpace ℝ ι) :
    Δ (coordinateCylinderCorrection i j) z = -4 := by
  have h₁ : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ ι => 16 - (y i) ^ 2) z := by fun_prop
  have h₂ : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ ι => (y j) ^ 2) z := by fun_prop
  have hi : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ ι => (y i) ^ 2) z := by fun_prop
  have hc : ContDiffAt ℝ 2 (fun _ : EuclideanSpace ℝ ι => (16 : ℝ)) z := contDiffAt_const
  change (Laplacian.laplacian ((fun y : EuclideanSpace ℝ ι => 16 - (y i) ^ 2) -
    (fun y : EuclideanSpace ℝ ι => (y j) ^ 2)) : EuclideanSpace ℝ ι → ℝ) z = -4
  rw [h₁.laplacian_sub h₂]
  have he := hc.laplacian_sub hi
  simp only [Pi.sub_def] at he
  rw [he, laplacian_const, laplacian_euclidean_coordinate_square,
    laplacian_euclidean_coordinate_square]
  norm_num

/-- The source's quadratic correction converts a weak upper Laplacian
bound for the energy into a nonnegative classical superharmonic function.
The index type includes the energy construction's `Fin 1 × Fin 3` time block. -/
theorem corrected_energy_of_weak_bound (i j : ι)
    {F : EuclideanSpace ℝ ι → ℝ} {U : Set (EuclideanSpace ℝ ι)}
    (hU : IsOpen U) (hF : ContDiffOn ℝ 2 F U) {δ : ℝ} (hδ : 0 ≤ δ)
    (hweak : ∀ η : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ ∞ η → HasCompactSupport η →
      tsupport η ⊆ U → (∀ x, 0 ≤ η x) →
      (∫ x, Δ η x * F x) ≤ δ * ∫ x, η x)
    {z : EuclideanSpace ℝ ι} (hz : z ∈ U) (hnonneg : 0 ≤ F z)
    (hrad : (z i) ^ 2 + (z j) ^ 2 ≤ 16) :
    0 ≤ F z + (δ / 4) * coordinateCylinderCorrection i j z ∧
      Δ (fun y => F y + (δ / 4) * coordinateCylinderCorrection i j y) z ≤ 0 := by
  have hFz := (hF z hz).contDiffAt (hU.mem_nhds hz)
  have hΔ := laplacian_le_of_weak_inequality_on hU hF hweak z hz
  constructor
  · exact add_nonneg hnonneg (mul_nonneg (by positivity)
      (by dsimp [coordinateCylinderCorrection]; linarith))
  · have hC := (contDiff_coordinateCylinderCorrection i j).contDiffAt (x := z)
    have he := hFz.laplacian_add (hC.const_smul (δ / 4))
    simp only [Pi.add_def] at he
    change Δ (fun y => F y + (δ / 4) • coordinateCylinderCorrection i j y) z ≤ 0
    rw [he]
    have hs := laplacian_smul (δ / 4) hC
    simp only [Pi.smul_def] at hs
    rw [hs, laplacian_coordinateCylinderCorrection, smul_eq_mul]
    linarith

end OAI.Analysis.PDE.Concentration
