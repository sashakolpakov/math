import OAI.Geometry.Nikodym.Beltrami.Metric

noncomputable section
namespace OAI.Geometry.Nikodym

open Matrix _root_.MeasureTheory
open scoped RealInnerProductSpace ENNReal

/-- Coordinate matrix of the Beltrami metric. -/
def beltramiMatrix {n : ℕ} (κ : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  (beltramiDenominator κ x)⁻¹ •
    (1 + vecMulVec (fun i => -(κ / beltramiDenominator κ x) * x i) x)

theorem beltramiMatrix_apply {n : ℕ} (κ : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (i j : Fin n) :
    beltramiMatrix κ x i j =
      ((beltramiDenominator κ x) * (if i = j then 1 else 0) - κ * x i * x j) /
        beltramiDenominator κ x ^ 2 := by
  simp only [beltramiMatrix,Matrix.smul_apply,Matrix.add_apply,Matrix.one_apply,
    vecMulVec_apply,smul_eq_mul]
  by_cases hq : beltramiDenominator κ x = 0
  · simp [hq]
  · field_simp
    ring

/-- The Riemannian volume density follows from the actual metric determinant,
not from an assumed bounded-Jacobian chart. -/
theorem det_beltramiMatrix {n : ℕ} (κ : ℝ) (x : EuclideanSpace ℝ (Fin n))
    (hq : beltramiDenominator κ x ≠ 0) :
    (beltramiMatrix κ x).det = (beltramiDenominator κ x)⁻¹ ^ (n+1) := by
  rw [beltramiMatrix,Matrix.det_smul,Matrix.vecMulVec_eq Unit,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hs : x ⬝ᵥ (fun i => -(κ / beltramiDenominator κ x) * x i) =
      -(κ / beltramiDenominator κ x) * ‖x‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,dotProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hs,Fintype.card_fin,pow_succ]
  congr 1
  dsimp [beltramiDenominator] at hq ⊢
  field_simp
  ring

def beltramiVolumeDensity {n : ℕ} (κ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt (beltramiMatrix κ x).det

def beltramiVolume {n : ℕ} (κ : ℝ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  volume.withDensity (fun x => ENNReal.ofReal (beltramiVolumeDensity κ x))

theorem beltramiVolumeDensity_pos {n : ℕ} {κ : ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hq : 0 < beltramiDenominator κ x) : 0 < beltramiVolumeDensity κ x := by
  rw [beltramiVolumeDensity,det_beltramiMatrix κ x hq.ne']
  exact Real.sqrt_pos.2 (pow_pos (inv_pos.2 hq) _)

theorem beltramiVolumeDensity_small_bounds {n : ℕ} {κ : ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : |κ| * ‖x‖^2 ≤ 1/2) :
    Real.sqrt ((2/3 : ℝ)^(n+1)) ≤ beltramiVolumeDensity κ x ∧
      beltramiVolumeDensity κ x ≤ Real.sqrt ((2 : ℝ)^(n+1)) := by
  obtain ⟨hl,hu⟩ := beltramiDenominator_small hx
  have hq : 0 < beltramiDenominator κ x := lt_of_lt_of_le (by norm_num) hl
  have hinvl : (2/3 : ℝ) ≤ (beltramiDenominator κ x)⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ hq).2
    linarith
  have hinvu : (beltramiDenominator κ x)⁻¹ ≤ (2 : ℝ) := by
    rw [← one_div]
    apply (div_le_iff₀ hq).2
    linarith
  rw [beltramiVolumeDensity,det_beltramiMatrix κ x hq.ne']
  constructor
  · exact Real.sqrt_le_sqrt (pow_le_pow_left₀ (by norm_num) hinvl _)
  · exact Real.sqrt_le_sqrt (pow_le_pow_left₀ (inv_nonneg.2 hq.le) hinvu _)

/-- Uniform comparison with Lebesgue volume on an actual small chart. -/
theorem beltramiVolume_restrict_bounds {n : ℕ} {κ : ℝ}
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S)
    (hsmall : ∀ x ∈ S, |κ| * ‖x‖^2 ≤ 1/2) :
    ENNReal.ofReal (Real.sqrt ((2/3 : ℝ)^(n+1))) • volume.restrict S ≤
      (beltramiVolume κ).restrict S ∧
    (beltramiVolume κ).restrict S ≤
      ENNReal.ofReal (Real.sqrt ((2 : ℝ)^(n+1))) • volume.restrict S := by
  rw [beltramiVolume,restrict_withDensity hS]
  constructor
  · rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hS] with x hx
    exact ENNReal.ofReal_le_ofReal (beltramiVolumeDensity_small_bounds (hsmall x hx)).1
  · rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hS] with x hx
    exact ENNReal.ofReal_le_ofReal (beltramiVolumeDensity_small_bounds (hsmall x hx)).2

end OAI.Geometry.Nikodym
