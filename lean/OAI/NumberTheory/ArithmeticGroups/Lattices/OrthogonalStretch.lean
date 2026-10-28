import Mathlib

/-! # Orthogonal Stretch -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalStretch.Construction

noncomputable section

/-! Stretching orthogonal subspaces: determinant and norm calculations for
the ellipsoids used in lattice compactness. -/

open scoped Classical
open Set _root_.Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

def orthogonalStretch (W : Submodule ℝ E) (a b : ℝ) : E →ₗ[ℝ] E :=
  let e := W.prodEquivOfIsCompl Wᗮ W.isCompl_orthogonal
  e.toLinearMap.comp ((a • (LinearMap.id : W →ₗ[ℝ] W)).prodMap
    (b • (LinearMap.id : Wᗮ →ₗ[ℝ] Wᗮ))) |>.comp e.symm.toLinearMap

theorem orthogonalStretch_apply (W : Submodule ℝ E) (a b : ℝ) (x : E) :
    orthogonalStretch W a b x = a • W.starProjection x + b • Wᗮ.starProjection x := by
  let e := W.prodEquivOfIsCompl Wᗮ W.isCompl_orthogonal
  have he : e.symm x = (W.orthogonalProjectionOnto x, Wᗮ.orthogonalProjectionOnto x) := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (W.starProjection_add_starProjection_orthogonal x).symm
  change e (((a • (LinearMap.id : W →ₗ[ℝ] W)).prodMap
    (b • (LinearMap.id : Wᗮ →ₗ[ℝ] Wᗮ))) (e.symm x)) = _
  rw [he]
  rfl

theorem orthogonalStretch_det (W : Submodule ℝ E) (a b : ℝ) :
    (orthogonalStretch W a b).det = a ^ finrank ℝ W * b ^ finrank ℝ Wᗮ := by
  rw [orthogonalStretch, LinearMap.comp_assoc, LinearMap.det_conj, LinearMap.det_prodMap]
  simp [LinearMap.det_smul]

theorem orthogonalStretch_perpendicular (W : Submodule ℝ E) (a b : ℝ) (x : E) :
    Wᗮ.starProjection (orthogonalStretch W a b x) = b • Wᗮ.starProjection x := by
  rw [orthogonalStretch_apply, map_add, map_smul, map_smul]
  have hz : Wᗮ.starProjection (W.starProjection x) = 0 :=
    Submodule.starProjection_orthogonal_apply_eq_zero (W.starProjection_apply_mem x)
  rw [hz, smul_zero, zero_add]
  congr 1
  exact Submodule.starProjection_eq_self_iff.mpr (Wᗮ.starProjection_apply_mem x)

theorem orthogonalStretch_mem_iff (W : Submodule ℝ E) (a : ℝ) {b : ℝ} (hb : b ≠ 0)
    (x : E) : orthogonalStretch W a b x ∈ W ↔ x ∈ W := by
  have hz (y : E) : Wᗮ.starProjection y = 0 ↔ y ∈ W := by
    change (Wᗮ.orthogonalProjectionOnto y).val = 0 ↔ _
    rw [Submodule.coe_eq_zero, Submodule.orthogonalProjectionOnto_eq_zero_iff,
      Submodule.orthogonal_orthogonal]
  rw [← hz, orthogonalStretch_perpendicular, smul_eq_zero, or_iff_right hb, hz]

theorem orthogonalStretch_norm_le (W : Submodule ℝ E) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (x : E) :
    ‖orthogonalStretch W a b x‖ ≤ (a + b) * ‖x‖ := by
  rw [orthogonalStretch_apply]
  calc
    ‖a • W.starProjection x + b • Wᗮ.starProjection x‖ ≤
        ‖a • W.starProjection x‖ + ‖b • Wᗮ.starProjection x‖ := norm_add_le _ _
    _ = a * ‖W.starProjection x‖ + b * ‖Wᗮ.starProjection x‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * ‖x‖ + b * ‖x‖ := add_le_add
      (mul_le_mul_of_nonneg_left (W.norm_starProjection_apply_le x) ha)
      (mul_le_mul_of_nonneg_left (Wᗮ.norm_starProjection_apply_le x) hb)
    _ = (a + b) * ‖x‖ := (add_mul _ _ _).symm

theorem orthogonalStretch_of_mem (W : Submodule ℝ E) (a b : ℝ) {x : E} (hx : x ∈ W) :
    orthogonalStretch W a b x = a • x := by
  rw [orthogonalStretch_apply, Submodule.starProjection_eq_self_iff.mpr hx,
    Submodule.starProjection_orthogonal_apply_eq_zero hx, smul_zero, add_zero]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalStretch.Construction
