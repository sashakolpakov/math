import OAI.Analysis.PDE.Dirichlet.HessianBounds
import OAI.Analysis.PDE.Dirichlet.QuaternionCoordinates

open scoped InnerProductSpace

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion

section Inner
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def realTangentProjection (ν v : E) : E := v - ⟪ν, v⟫_ℝ • ν

theorem realTangentProjection_tangent {ν : E} (hν : ‖ν‖ = 1) (v : E) :
    ⟪ν, realTangentProjection ν v⟫_ℝ = 0 := by
  simp [realTangentProjection, inner_sub_right, real_inner_smul_right,
    hν]

theorem realTangentProjection_norm {ν v : E} (hν : ‖ν‖ = 1) (hv : ‖v‖ ≤ 1) :
    ‖realTangentProjection ν v‖ ≤ 2 := by
  have hi : |⟪ν, v⟫_ℝ| ≤ 1 := (abs_real_inner_le_norm ν v).trans (by simpa [hν] using hv)
  calc
    _ ≤ ‖v‖ + ‖⟪ν, v⟫_ℝ • ν‖ := norm_sub_le _ _
    _ = ‖v‖ + |⟪ν, v⟫_ℝ| := by rw [norm_smul, Real.norm_eq_abs, hν, mul_one]
    _ ≤ 2 := by linarith

/-- Once tangential and mixed entries are controlled, subtracting the
single unknown normal-normal entry leaves a bounded bilinear form. -/
theorem normal_remainder_abs_bound (H : E →L[ℝ] E →L[ℝ] ℝ) {ν v w : E}
    (hν : ‖ν‖ = 1) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hH : ∀ x y, H x y = H y x) {T M : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M)
    (ht : ∀ x y, ⟪ν, x⟫_ℝ = 0 → ⟪ν, y⟫_ℝ = 0 → |H x y| ≤ T * ‖x‖ * ‖y‖)
    (hm : ∀ x, ⟪ν, x⟫_ℝ = 0 → |H ν x| ≤ M * ‖x‖) :
    |H v w - H ν ν * ⟪ν, v⟫_ℝ * ⟪ν, w⟫_ℝ| ≤ 4 * T + 4 * M := by
  let x := realTangentProjection ν v
  let y := realTangentProjection ν w
  have hx : ‖x‖ ≤ 2 := realTangentProjection_norm hν hv
  have hy : ‖y‖ ≤ 2 := realTangentProjection_norm hν hw
  have hx0 : ⟪ν, x⟫_ℝ = 0 := realTangentProjection_tangent hν v
  have hy0 : ⟪ν, y⟫_ℝ = 0 := realTangentProjection_tangent hν w
  have hav : |⟪ν, v⟫_ℝ| ≤ 1 := (abs_real_inner_le_norm ν v).trans (by simpa [hν] using hv)
  have haw : |⟪ν, w⟫_ℝ| ≤ 1 := (abs_real_inner_le_norm ν w).trans (by simpa [hν] using hw)
  have hxy : |H x y| ≤ 4 * T := by
    have hprod : ‖x‖ * ‖y‖ ≤ 4 := by
      calc
        _ ≤ 2 * 2 := mul_le_mul hx hy (norm_nonneg _) (by norm_num)
        _ = 4 := by norm_num
    calc
      _ ≤ T * ‖x‖ * ‖y‖ := ht x y hx0 hy0
      _ = T * (‖x‖ * ‖y‖) := mul_assoc _ _ _
      _ ≤ T * 4 := mul_le_mul_of_nonneg_left hprod hT
      _ = 4 * T := mul_comm _ _
  have hmx : |H ν x| ≤ 2 * M := (hm x hx0).trans (by nlinarith)
  have hmy : |H ν y| ≤ 2 * M := (hm y hy0).trans (by nlinarith)
  have hxterm : |⟪ν, w⟫_ℝ * H ν x| ≤ 2 * M := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right haw (abs_nonneg _)).trans (by simpa using hmx)
  have hyterm : |⟪ν, v⟫_ℝ * H ν y| ≤ 2 * M := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hav (abs_nonneg _)).trans (by simpa using hmy)
  have heq : H v w - H ν ν * ⟪ν, v⟫_ℝ * ⟪ν, w⟫_ℝ =
      H x y + ⟪ν, v⟫_ℝ * H ν y + ⟪ν, w⟫_ℝ * H ν x := by
    simp only [x, y, realTangentProjection, map_sub, map_smul, sub_apply, smul_apply,
      smul_eq_mul]
    rw [hH v ν]
    ring
  rw [heq]
  calc
    _ ≤ |H x y + ⟪ν, v⟫_ℝ * H ν y| + |⟪ν, w⟫_ℝ * H ν x| := abs_add_le _ _
    _ ≤ (|H x y| + |⟪ν, v⟫_ℝ * H ν y|) + |⟪ν, w⟫_ℝ * H ν x| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ 4 * T + 4 * M := by linarith

end Inner
end OAI.Analysis.PDE.Dirichlet
