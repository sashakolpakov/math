import OAI.Analysis.PDE.Elliptic.Boundary.FlatJet
import OAI.Analysis.PDE.Elliptic.Boundary.RemainderNorm

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem linear_form_tangent_bound (ell : E →L[ℝ] ℝ) (v : E) {M : ℝ}
    (hb : ∀ e, ‖e‖ ≤ 1 → inner ℝ v e = 0 → |ell e| ≤ M) :
    ∀ e, inner ℝ v e = 0 → |ell e| ≤ M * ‖e‖ := by
  intro e he
  by_cases hz : e = 0
  · simp [hz]
  have hp : 0 < ‖e‖ := norm_pos_iff.mpr hz
  let q := ‖e‖⁻¹ • e
  have hq : ‖q‖ ≤ 1 := by simp [q, norm_smul, hp.ne']
  have hvq : inner ℝ v q = 0 := by simp [q, real_inner_smul_right, he]
  have h := hb q hq hvq
  have heq : ell q = ‖e‖⁻¹ * ell e := by simp [q]
  rw [heq, abs_mul, abs_of_pos (inv_pos.mpr hp)] at h
  have hh := mul_le_mul_of_nonneg_left h hp.le
  calc
    |ell e| = ‖e‖ * (‖e‖⁻¹ * |ell e|) := by field_simp
    _ ≤ ‖e‖ * M := hh
    _ = M * ‖e‖ := mul_comm _ _

theorem flat_hessian_remainder_bound {w : E → ℝ} (hw : ContDiff ℝ 2 w)
    {v z z' : E} (hv : ‖v‖ = 1) (hz : ‖z‖ < 1) (hz' : ‖z'‖ < 1)
    (hvz : inner ℝ v z = 0) (hvz' : inner ℝ v z' = 0)
    (hzero : ∀ y, ‖y‖ ≤ 1 → inner ℝ v y = 0 → w y = 0)
    {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ e, ‖e‖ ≤ 1 → inner ℝ v e = 0 →
      |fderiv ℝ (fderiv ℝ w) z v e - fderiv ℝ (fderiv ℝ w) z' v e| ≤ M) :
    let H := fderiv ℝ (gradient w) z - fderiv ℝ (gradient w) z'
    ‖H - inner ℝ (H v) v • rankOne ℝ v v‖ ≤ 4 * M := by
  dsimp only
  let H := fderiv ℝ (gradient w) z - fderiv ℝ (gradient w) z'
  have hH : H.toLinearMap.IsSymmetric :=
    (fderiv_gradient_isSymmetric hw z).sub (fderiv_gradient_isSymmetric hw z')
  have heval (a b : E) : inner ℝ (H a) b =
      fderiv ℝ (fderiv ℝ w) z a b - fderiv ℝ (fderiv ℝ w) z' a b := by
    simp only [H, sub_apply, inner_sub_left, inner_fderiv_gradient_at hw.contDiffAt]
  have ht (a b : E) (ha : inner ℝ v a = 0) (hb : inner ℝ v b = 0) : inner ℝ (H a) b = 0 := by
    rw [heval, flat_boundary_second_jet hw hv hz hvz ha hb hzero,
      flat_boundary_second_jet hw hv hz' hvz' ha hb hzero, sub_self]
  have hm' : ∀ e, inner ℝ v e = 0 → |inner ℝ (H v) e| ≤ M * ‖e‖ := by
    apply linear_form_tangent_bound ((toDual ℝ E) (H v)) v
    intro e he hve
    change |inner ℝ (H v) e| ≤ M
    rw [heval]
    exact hm e he hve
  simpa [H] using normal_remainder_operator_norm H hv hH (le_refl 0) hM
    (fun a b ha hb => by rw [ht a b ha hb]; simp) hm'

end OAI.Analysis.PDE.Elliptic
