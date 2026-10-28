import OAI.Analysis.PDE.Concentration.Harmonic
import OAI.Analysis.PDE.Dirichlet.Hessian

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Filter InnerProductSpace Laplacian
open scoped ENNReal Topology

theorem hessian_linear_square {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) (x v w : E) :
    (fderiv ℝ (fderiv ℝ (fun y => (L y) ^ 2)) x v) w = 2 * L v * L w := by
  simp_rw [pow_two]
  rw [OAI.Analysis.PDE.Dirichlet.hessian_mul L.contDiff L.contDiff]
  have hD : fderiv ℝ L = fun _ => L := funext fun y => L.fderiv
  rw [hD]
  have hDD : fderiv ℝ (fun _ : E => L) x = 0 := (hasFDerivAt_const L x).fderiv
  rw [hDD]
  simp only [zero_apply, mul_zero, zero_add]
  ring

theorem laplacian_coordinate_square {n : ℕ} (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    Δ (fun y : EuclideanSpace ℝ (Fin n) => (y i) ^ 2) x = 2 := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun (Fin n) ℝ)]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  change (∑ j : Fin n, (fderiv ℝ (fderiv ℝ (fun y => (y i) ^ 2)) x
    ((EuclideanSpace.basisFun (Fin n) ℝ) j)) ((EuclideanSpace.basisFun (Fin n) ℝ) j)) = 2
  have hh (v w : EuclideanSpace ℝ (Fin n)) :
      (fderiv ℝ (fderiv ℝ (fun y => (y i) ^ 2)) x v) w = 2 * v i * w i :=
    hessian_linear_square (EuclideanSpace.proj i) x v w
  simp_rw [hh]
  simp [EuclideanSpace.basisFun_apply, PiLp.single_apply]

/-- The radial correction in the two imaginary time coordinates. -/
def cylinderCorrection (z : EuclideanSpace ℝ (Fin 3)) : ℝ := 16 - (z 1) ^ 2 - (z 2) ^ 2

theorem contDiff_cylinderCorrection : ContDiff ℝ 2 cylinderCorrection := by
  unfold cylinderCorrection
  fun_prop

theorem laplacian_cylinderCorrection (z : EuclideanSpace ℝ (Fin 3)) :
    Δ cylinderCorrection z = -4 := by
  have h₁ : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) => 16 - (y 1) ^ 2) z := by fun_prop
  have h₂ : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) => (y 2) ^ 2) z := by fun_prop
  have hsq : ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin 3) => (y 1) ^ 2) z := by fun_prop
  change (Laplacian.laplacian ((fun y : EuclideanSpace ℝ (Fin 3) => 16 - (y 1) ^ 2) -
    (fun y : EuclideanSpace ℝ (Fin 3) => (y 2) ^ 2))) z = -4
  rw [h₁.laplacian_sub h₂]
  have hc : ContDiffAt ℝ 2 (fun _ : EuclideanSpace ℝ (Fin 3) => (16 : ℝ)) z := contDiffAt_const
  have he := hc.laplacian_sub hsq
  simp only [Pi.sub_def] at he
  rw [he,
    laplacian_const, laplacian_coordinate_square, laplacian_coordinate_square]
  norm_num

/-- A Laplacian error `δ` is canceled by `δ/4` times the precise quadratic
correction from the manuscript; nonnegativity is retained inside radius four. -/
theorem corrected_energy_superharmonic {F : EuclideanSpace ℝ (Fin 3) → ℝ}
    {δ : ℝ} (hδ : 0 ≤ δ) {z : EuclideanSpace ℝ (Fin 3)}
    (hF : ContDiffAt ℝ 2 F z) (hΔ : Δ F z ≤ δ) (hnonneg : 0 ≤ F z)
    (hz : (z 1) ^ 2 + (z 2) ^ 2 ≤ 16) :
    0 ≤ F z + (δ / 4) * cylinderCorrection z ∧
      Δ (fun y => F y + (δ / 4) * cylinderCorrection y) z ≤ 0 := by
  constructor
  · exact add_nonneg hnonneg (mul_nonneg (by positivity) (by dsimp [cylinderCorrection]; linarith))
  · have hC : ContDiffAt ℝ 2 cylinderCorrection z := contDiff_cylinderCorrection.contDiffAt
    have he := hF.laplacian_add (hC.const_smul (δ / 4))
    simp only [Pi.add_def] at he
    change Δ (fun y => F y + (δ / 4) • cylinderCorrection y) z ≤ 0
    rw [he]
    have hs := laplacian_smul (δ / 4) hC
    simp only [Pi.smul_def] at hs
    rw [hs, laplacian_cylinderCorrection, smul_eq_mul]
    linarith

/-- Fatou's lemma supplies the unbounded-cylinder stopping limit: bounded
stopping inequalities and almost-sure convergence suffice, with no uniform
integrability hypothesis for the nonnegative corrected energy. -/
theorem supermean_of_stopped_supermeans {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {G : ℕ → Ω → ℝ≥0∞} {g : Ω → ℝ≥0∞} {C : ℝ≥0∞}
    (hG : ∀ j, Measurable (G j)) (hlim : ∀ᵐ ω ∂P, Tendsto (fun j => G j ω) atTop (𝓝 (g ω)))
    (hbound : ∀ j, ∫⁻ ω, G j ω ∂P ≤ C) : (∫⁻ ω, g ω ∂P) ≤ C := by
  calc
    _ = ∫⁻ ω, liminf (fun j => G j ω) atTop ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hlim] with ω hω
      exact hω.liminf_eq.symm
    _ ≤ liminf (fun j => ∫⁻ ω, G j ω ∂P) atTop := lintegral_liminf_le hG
    _ ≤ C := liminf_le_of_frequently_le (Frequently.of_forall hbound)

end OAI.Analysis.PDE.Concentration
