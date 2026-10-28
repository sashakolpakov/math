import OAI.Analysis.PDE.Elliptic.Boundary.Flattening
import OAI.Analysis.PDE.Elliptic.Boundary.PullbackEllipticity

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_inward_unit_normal (g : E →L[ℝ] ℝ) (hg : g ≠ 0) :
    ∃ (v : E) (c : ℝ), ‖v‖ = 1 ∧ 0 < c ∧ ∀ y, g y = -c * inner ℝ v y := by
  let ξ := (toDual ℝ E).symm g
  have hξ : ξ ≠ 0 := by
    intro hz
    have h := congrArg (toDual ℝ E) hz
    apply hg
    simpa [ξ] using h
  have hp : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  let v := -(‖ξ‖⁻¹ : ℝ) • ξ
  refine ⟨v, ‖ξ‖, ?_, hp, ?_⟩
  · simp [v, norm_smul, hp.ne']
  · intro y
    have he : inner ℝ ξ y = g y := by
      change ((toDual ℝ E) ((toDual ℝ E).symm g)) y = _
      rw [LinearIsometryEquiv.apply_symm_apply]
    simp only [v, real_inner_smul_left, he]
    field_simp

omit [FiniteDimensional ℝ E] in
theorem inverse_lower_norm (T D : E →L[ℝ] E) {C : ℝ}
    (hDT : D.comp T = ContinuousLinearMap.id ℝ E) (hD : ‖D‖ ≤ C) (v : E) :
    ‖v‖ ≤ C * ‖T v‖ := by
  have h := D.le_opNorm (T v)
  have he : D (T v) = v := congrArg (fun L : E →L[ℝ] E => L v) hDT
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _))

theorem pullbackEllipticOperator_bounds_of_inverse (T D A : E →L[ℝ] E)
    {C lam L : ℝ} (hC : 0 < C) (hlam : 0 ≤ lam) (hL : 0 ≤ L)
    (hTD : T.comp D = ContinuousLinearMap.id ℝ E) (hT : ‖T‖ ≤ C) (hD : ‖D‖ ≤ C)
    (hlo : ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A v))
    (hhi : ∀ v, inner ℝ v (A v) ≤ L * ‖v‖ ^ 2) :
    ∀ v, (lam / C ^ 2) * ‖v‖ ^ 2 ≤ inner ℝ v (pullbackEllipticOperator T A v) ∧
      inner ℝ v (pullbackEllipticOperator T A v) ≤ (L * C ^ 2) * ‖v‖ ^ 2 := by
  intro v
  rw [pullbackEllipticOperator_form]
  have hda : D.adjoint.comp T.adjoint = ContinuousLinearMap.id ℝ E := by
    have h := congrArg (ContinuousLinearMap.adjoint : (E →L[ℝ] E) → (E →L[ℝ] E)) hTD
    simpa [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using h
  have hd : ‖v‖ ≤ C * ‖T.adjoint v‖ := inverse_lower_norm T.adjoint D.adjoint hda
    (by simpa only [ContinuousLinearMap.adjoint.norm_map] using hD) v
  have ht : ‖T.adjoint v‖ ≤ C * ‖v‖ :=
    (T.adjoint.le_opNorm v).trans (mul_le_mul_of_nonneg_right
      (by simpa only [ContinuousLinearMap.adjoint.norm_map] using hT) (norm_nonneg v))
  have hsq : ‖v‖ ^ 2 ≤ C ^ 2 * ‖T.adjoint v‖ ^ 2 := by nlinarith [mul_self_le_mul_self (norm_nonneg v) hd]
  have hsq' : ‖T.adjoint v‖ ^ 2 ≤ C ^ 2 * ‖v‖ ^ 2 := by nlinarith [mul_self_le_mul_self (norm_nonneg (T.adjoint v)) ht]
  constructor
  · apply le_trans _ (hlo (T.adjoint v))
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (sq_pos_of_pos hC)).mpr
    have hh := mul_le_mul_of_nonneg_left hsq hlam
    nlinarith
  · exact (hhi (T.adjoint v)).trans (by nlinarith [mul_le_mul_of_nonneg_left hsq' hL])

end OAI.Analysis.PDE.Elliptic
