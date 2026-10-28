import OAI.Analysis.PDE.Dirichlet.QuaternionCoordinates
import OAI.Analysis.PDE.Dirichlet.RigidBoundary

open scoped Matrix RealInnerProductSpace

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion

/-- Construction of the quaternionic rigid field from a nonzero real normal
covector and the actual second derivative in a fixed tangent direction. -/
theorem exists_adapted_quaternionic_field {n : ℕ}
    (g : CoordinateSpace n 4 →L[ℝ] ℝ) (hg : g ≠ 0)
    (H : CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 →L[ℝ] ℝ)
    (e : CoordinateSpace n 4) :
    ∃ (c : ℝ) (ν : CoordinateSpace n 4) (A : Matrix (Fin n) (Fin n) Q),
      0 < c ∧ ‖ν‖ = 1 ∧ g = c • innerSL ℝ ν ∧ Aᴴ = -A ∧
      g (realMatrixAction (realRepresentation A) ν) = 0 ∧
      ∀ w, g w = 0 → g (realMatrixAction (realRepresentation A) w) + H w e = 0 := by
  let G := (InnerProductSpace.toDual ℝ (CoordinateSpace n 4)).symm g
  let c := ‖G‖
  have hc : 0 < c := by
    dsimp [c, G]
    rw [(InnerProductSpace.toDual ℝ (CoordinateSpace n 4)).symm.norm_map]
    exact norm_pos_iff.mpr hg
  let ν : CoordinateSpace n 4 := c⁻¹ • G
  have hν : ‖ν‖ = 1 := by
    change ‖c⁻¹ • G‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
    exact inv_mul_cancel₀ hc.ne'
  have hG (w) : ⟪G, w⟫ = g w := InnerProductSpace.toDual_symm_apply
  have hgval (w) : g w = c * ⟪ν, w⟫ := by
    dsimp [ν]
    rw [real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul, hG]
  have hgform : g = c • innerSL ℝ ν := by
    ext w
    simpa only [smul_apply, innerSL_apply_apply, smul_eq_mul] using hgval w
  let z := (InnerProductSpace.toDual ℝ (CoordinateSpace n 4)).symm (H.flip e)
  have hz (w) : ⟪z, w⟫ = H w e := InnerProductSpace.toDual_symm_apply
  let v : CoordinateSpace n 4 := c⁻¹ • (z - ⟪ν, z⟫ • ν)
  have hv : ⟪ν, v⟫ = 0 := by
    simp [v, inner_sub_right, real_inner_smul_right, hν]
  obtain ⟨A, hA, hAv⟩ := exists_quaternionic_rotation ν v hν hv
  refine ⟨c, ν, A, hc, hν, hgform, hA, ?_, ?_⟩
  · rw [hAv, hgval, hv, mul_zero]
  intro w hw
  have hwν : ⟪ν, w⟫ = 0 := by
    have hw' : c * ⟪ν, w⟫ = 0 := (hgval w).symm.trans hw
    exact (mul_eq_zero.mp hw').resolve_left hc.ne'
  have hvw : ⟪v, w⟫ = c⁻¹ * H w e := by
    simp only [v, real_inner_smul_left, inner_sub_left, hwν, mul_zero, sub_zero, hz]
  rw [hgval, realMatrixAction_skew (realRepresentation_skew hA), hAv, hvw]
  rw [mul_neg, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  ring

/-- The adapted rigid field, and hence its quadratic boundary vanishing, are
constructed from the defining function. No choice of a boundary chart or
unproved cancellation estimate is an input. -/
theorem exists_adapted_boundary_field {n : ℕ} {r : CoordinateSpace n 4 → ℝ}
    (hr : ContDiff ℝ 3 r) (hr0 : r 0 = 0) (hr' : fderiv ℝ r 0 ≠ 0)
    (e : CoordinateSpace n 4) (he : fderiv ℝ r 0 e = 0) :
    ∃ (c : ℝ) (ν : CoordinateSpace n 4) (A : Matrix (Fin n) (Fin n) Q) (C R : ℝ),
      0 < c ∧ ‖ν‖ = 1 ∧ fderiv ℝ r 0 = c • innerSL ℝ ν ∧ Aᴴ = -A ∧
      fderiv ℝ r 0 (realMatrixAction (realRepresentation A) ν) = 0 ∧
      0 < C ∧ 0 < R ∧ ∀ x, ‖x‖ ≤ R → r x = 0 →
        |affineDerivative r e (realMatrixAction (realRepresentation A)) x| ≤ C * ‖x‖ ^ 2 := by
  obtain ⟨c, ν, A, hc, hν, hg, hA, hAn, hjet⟩ :=
    exists_adapted_quaternionic_field (fderiv ℝ r 0) hr' (fderiv ℝ (fderiv ℝ r) 0) e
  obtain ⟨C, R, hC, hR, hquad⟩ :=
    affineDerivative_quadratic_on_boundary hr hr0 hr' e
      (realMatrixAction (realRepresentation A)) he hjet
  exact ⟨c, ν, A, C, R, hc, hν, hg, hA, hAn, hC, hR, hquad⟩

end OAI.Analysis.PDE.Dirichlet
