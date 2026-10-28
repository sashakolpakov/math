import OAI.Geometry.Nikodym.FlowJacobi
import OAI.Geometry.Nikodym.Jacobi.RadialCenter

noncomputable section
namespace OAI.Geometry.Nikodym.LocalGeodesicFlow

open Set
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {g : SmoothCoordinateMetric E} {x₀ : E} (F : LocalGeodesicFlow g x₀)

def normalizedEndpoint (R : E ≃L[ℝ] E) (t : ℝ) (ξ : E) : E :=
  F.position (t⁻¹ • R.symm ξ,t)

theorem contDiffAt_normalizedEndpoint (R : E ≃L[ℝ] E) {t : ℝ}
    (ht : t ∈ Ioo (-F.radius) F.radius) {ξ : E}
    (hξ : t⁻¹ • R.symm ξ ∈ F.velocities) :
    ContDiffAt ℝ ∞ (F.normalizedEndpoint R t) ξ := by
  have hc : ContDiffAt ℝ ∞ (fun w => F.position (w,t)) (t⁻¹ • R.symm ξ) :=
    (F.contDiffAt_state_slice hξ ht).fst
  have hh := hc.comp ξ (R.symm.contDiff.const_smul t⁻¹).contDiffAt
  exact hh

theorem fderiv_normalizedEndpoint (R : E ≃L[ℝ] E) {t : ℝ}
    (ht : t ∈ Ioo (-F.radius) F.radius) {ξ : E}
    (hξ : t⁻¹ • R.symm ξ ∈ F.velocities) (u : E) :
    fderiv ℝ (F.normalizedEndpoint R t) ξ u =
      fderiv ℝ (fun w => F.position (w,t)) (t⁻¹ • R.symm ξ) (t⁻¹ • R.symm u) := by
  have hd := ((F.contDiffAt_state_slice hξ ht).fst.differentiableAt (by simp)).hasFDerivAt
  have he := hd.comp ξ (R.symm.hasFDerivAt.const_smul t⁻¹)
  exact congrArg (fun L : E →L[ℝ] E => L u) he.fderiv

/-- Normal coordinates, with the actual base metric normalized and time
rescaled, have the exact space-form radial metric. -/
theorem normalizedEndpoint_metric {κ : ℝ} (hκ : g.HasConstantCurvature κ)
    (R : E ≃L[ℝ] E) (hR : ∀ u v, g.inner x₀ u v = inner ℝ (R u) (R v))
    {t : ℝ} (ht : t ∈ Ioo (-F.radius) F.radius) (ht0 : 0 < t)
    {ξ : E} (hξ : t⁻¹ • R.symm ξ ∈ F.velocities) (hξ0 : ξ ≠ 0) (u v : E) :
    g.inner (F.normalizedEndpoint R t ξ)
      (fderiv ℝ (F.normalizedEndpoint R t) ξ u)
      (fderiv ℝ (F.normalizedEndpoint R t) ξ v) =
      inner ℝ ξ u * inner ℝ ξ v / ‖ξ‖^2 +
        (curvatureSin κ ‖ξ‖ / ‖ξ‖)^2 *
          (inner ℝ u v - inner ℝ ξ u * inner ℝ ξ v / ‖ξ‖^2) := by
  have htne := ht0.ne'
  have hn := norm_ne_zero_iff.mpr hξ0
  have hw : t⁻¹ • R.symm ξ ≠ 0 := by
    intro hz
    have he := congrArg R hz
    simp only [map_smul,R.apply_symm_apply,map_zero] at he
    exact hξ0 ((smul_eq_zero.mp he).resolve_left (inv_ne_zero htne))
  have hq : g.inner x₀ (t⁻¹ • R.symm ξ) (t⁻¹ • R.symm ξ) = (‖ξ‖/t)^2 := by
    rw [hR]
    simp only [map_smul,R.apply_symm_apply,real_inner_self_eq_norm_sq,norm_smul,
      Real.norm_eq_abs,mul_pow,sq_abs]
    ring
  have hc : Real.sqrt (g.inner x₀ (t⁻¹ • R.symm ξ) (t⁻¹ • R.symm ξ)) = ‖ξ‖/t := by
    rw [hq,Real.sqrt_sq (div_nonneg (norm_nonneg _) ht0.le)]
  rw [F.fderiv_normalizedEndpoint R ht hξ u,F.fderiv_normalizedEndpoint R ht hξ v]
  change g.inner (F.position (t⁻¹ • R.symm ξ,t)) _ _ = _
  rw [F.endpoint_metric hκ hξ hw (t⁻¹ • R.symm u) (t⁻¹ • R.symm v) ht]
  rw [hc]
  simp only [hR,map_smul,R.apply_symm_apply,real_inner_smul_left,real_inner_smul_right]
  rw [div_mul_cancel₀ _ htne,real_inner_comm u ξ,real_inner_comm v ξ]
  field_simp


theorem normalizedEndpoint_metric_zero (R : E ≃L[ℝ] E)
    (hR : ∀ u v, g.inner x₀ u v = inner ℝ (R u) (R v))
    {t : ℝ} (ht : t ∈ Ioo (-F.radius) F.radius) (ht0 : t ≠ 0) (u v : E) :
    g.inner (F.normalizedEndpoint R t 0)
      (fderiv ℝ (F.normalizedEndpoint R t) 0 u)
      (fderiv ℝ (F.normalizedEndpoint R t) 0 v) = inner ℝ u v := by
  have hz : t⁻¹ • R.symm (0 : E) ∈ F.velocities := by simpa using F.zero_mem
  have hpos : F.normalizedEndpoint R t 0 = x₀ := by
    simpa only [LocalGeodesicFlow.normalizedEndpoint,map_zero,smul_zero,LocalGeodesicFlow.position] using
      congrArg Prod.fst (F.zero_state ht)
  have hd (w : E) : fderiv ℝ (F.normalizedEndpoint R t) 0 w = R.symm w := by
    rw [F.fderiv_normalizedEndpoint R ht hz,map_zero,smul_zero,
      (F.hasFDerivAt_position_slice_zero ht).fderiv]
    simp [smul_smul,ht0]
  rw [hpos,hd u,hd v,hR,R.apply_symm_apply,R.apply_symm_apply]

/-- The genuine exponential-coordinate metric and the projective radial
pullback of the Beltrami metric agree, including at the center. -/
theorem normalizedEndpoint_beltrami_metric {κ : ℝ} (hκ : g.HasConstantCurvature κ)
    (R : E ≃L[ℝ] E) (hR : ∀ u v, g.inner x₀ u v = inner ℝ (R u) (R v))
    {t : ℝ} (ht : t ∈ Ioo (-F.radius) F.radius) (ht0 : 0 < t)
    {ξ : E} (hξ : t⁻¹ • R.symm ξ ∈ F.velocities)
    (hcos : curvatureCos κ ‖ξ‖ ≠ 0) (u v : E) :
    g.inner (F.normalizedEndpoint R t ξ)
      (fderiv ℝ (F.normalizedEndpoint R t) ξ u)
      (fderiv ℝ (F.normalizedEndpoint R t) ξ v) =
      beltramiMetric κ (projectiveRadialMap κ ξ)
        (fderiv ℝ (projectiveRadialMap κ) ξ u)
        (fderiv ℝ (projectiveRadialMap κ) ξ v) := by
  by_cases hξ0 : ξ = 0
  · subst ξ
    rw [F.normalizedEndpoint_metric_zero R hR ht ht0.ne',
      projectiveRadialMap_pullback_metric_zero]
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ0
  have he : ‖(‖ξ‖⁻¹ : ℝ) • ξ‖ = 1 := by
    simp [norm_smul,hn.ne']
  have hid : ‖ξ‖ • (‖ξ‖⁻¹ • ξ) = ξ := by simp [smul_smul,hn.ne']
  have hh := projectiveRadialMap_pullback_metric κ ‖ξ‖ hn he hcos u v
  rw [hid] at hh
  rw [hh,F.normalizedEndpoint_metric hκ R hR ht ht0 hξ hξ0 u v]
  simp only [normalRadialMetric,real_inner_smul_left]
  ring

end OAI.Geometry.Nikodym.LocalGeodesicFlow
