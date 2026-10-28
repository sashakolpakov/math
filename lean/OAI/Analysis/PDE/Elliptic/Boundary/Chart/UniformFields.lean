import OAI.Analysis.PDE.Elliptic.Boundary.Chart.Fields

/-! Uniform bounds over all unit coordinate tangent fields.  These constants
depend on the chart and prescribed background, not on a solution. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_apply_unit {Q : E → E →L[ℝ] F} (hQ : ContDiff ℝ 2 Q)
    {e : E} (he : ‖e‖ ≤ 1) (x : E) {k : ℕ} (hk : k ≤ 2) :
    ‖iteratedFDeriv ℝ k (fun y => Q y e) x‖ ≤ ‖iteratedFDeriv ℝ k Q x‖ := by
  let L : (E →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F e
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f
    change ‖f e‖ ≤ 1 * ‖f‖
    calc
      ‖f e‖ ≤ ‖f‖ * ‖e‖ := f.le_opNorm e
      _ ≤ ‖f‖ * 1 := mul_le_mul_of_nonneg_left he (norm_nonneg _)
      _ = 1 * ‖f‖ := by ring
  have hk' : (k : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hk
  change ‖iteratedFDeriv ℝ k (L ∘ Q) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_left hQ.contDiffAt hk']
  exact (L.norm_compContinuousMultilinearMap_le _).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hL (norm_nonneg _))

theorem exists_C2_unit_apply_bounds {Q : E → E →L[ℝ] F} (hQ : ContDiff ℝ 2 Q)
    {K : Set E} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ e : E, ‖e‖ ≤ 1 → ∀ x ∈ K,
      ‖Q x e‖ ≤ C ∧ ‖fderiv ℝ (fun y => Q y e) x‖ ≤ C ∧
        ‖iteratedFDeriv ℝ 2 (fun y => Q y e) x‖ ≤ C := by
  have hc1 : Continuous (fun x => ‖iteratedFDeriv ℝ 1 Q x‖) :=
    continuous_iff_continuousAt.mpr fun x => (hQ.contDiffAt.continuousAt_iteratedFDeriv (by norm_num)).norm
  have hc2 : Continuous (fun x => ‖iteratedFDeriv ℝ 2 Q x‖) :=
    continuous_iff_continuousAt.mpr fun x => (hQ.contDiffAt.continuousAt_iteratedFDeriv (by norm_num)).norm
  obtain ⟨C0, hC0⟩ := hK.exists_bound_of_continuousOn hQ.continuous.continuousOn
  obtain ⟨C1, hC1⟩ := hK.exists_bound_of_continuousOn hc1.continuousOn
  obtain ⟨C2, hC2⟩ := hK.exists_bound_of_continuousOn hc2.continuousOn
  let C := max 1 (max C0 (max C1 C2))
  have h0 : C0 ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have h1 : C1 ≤ C := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h2 : C2 ≤ C := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro e he x hx
  refine ⟨?_, ?_, ?_⟩
  · have hb := norm_iteratedFDeriv_apply_unit hQ he x (k := 0) (by norm_num)
    simp only [norm_iteratedFDeriv_zero] at hb
    exact hb.trans ((hC0 x hx).trans h0)
  · have hb := norm_iteratedFDeriv_apply_unit hQ he x (k := 1) (by norm_num)
    simp only [norm_iteratedFDeriv_one] at hb
    exact hb.trans ((by simpa [norm_iteratedFDeriv_one] using hC1 x hx : ‖fderiv ℝ Q x‖ ≤ C1).trans h1)
  · have hc : ‖iteratedFDeriv ℝ 2 Q x‖ ≤ C2 := by simpa using hC2 x hx
    exact (norm_iteratedFDeriv_apply_unit hQ he x (by norm_num)).trans (hc.trans h2)

end General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_uniform_chart_field_bounds
    {G P : E → E} {B : E → ℝ} (hG : ContDiff ℝ 3 G) (hP : ContDiff ℝ 3 P)
    (hB : ContDiff ℝ 3 B) {K : Set E} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ e : E, ‖e‖ ≤ 1 → ∀ x ∈ K,
      ‖chartTangentField G P e x‖ ≤ C ∧
      ‖fderiv ℝ (chartTangentField G P e) x‖ ≤ C ∧
      ‖iteratedFDeriv ℝ 2 (chartTangentField G P e) x‖ ≤ C ∧
      ‖fderiv ℝ (fieldDerivative B (chartTangentField G P e)) x‖ ≤ C ∧
      ‖fderiv ℝ (gradient (fieldDerivative B (chartTangentField G P e))) x‖ ≤ C := by
  let Q : E → E →L[ℝ] E := fun y => fderiv ℝ G (P y)
  have hQ : ContDiff ℝ 2 Q := (hG.fderiv_right (by norm_num)).comp (hP.of_le (by norm_num))
  let R : E → E →L[ℝ] ℝ := fun y => (fderiv ℝ B y).comp (Q y)
  have hR : ContDiff ℝ 2 R := (hB.fderiv_right (by norm_num)).clm_comp hQ
  obtain ⟨C1, hC1, hb1⟩ := exists_C2_unit_apply_bounds hQ hK
  obtain ⟨C2, hC2, hb2⟩ := exists_C2_unit_apply_bounds hR hK
  refine ⟨max C1 C2, lt_max_of_lt_left hC1, ?_⟩
  intro e he x hx
  have h1 := hb1 e he x hx
  have h2 := hb2 e he x hx
  refine ⟨h1.1.trans (le_max_left _ _), h1.2.1.trans (le_max_left _ _),
    h1.2.2.trans (le_max_left _ _), h2.2.1.trans (le_max_right _ _), ?_⟩
  have hW : ContDiff ℝ 2 (fieldDerivative B (chartTangentField G P e)) :=
    contDiff_fieldDerivative hB (contDiff_chartTangentField hG hP e) (by norm_num)
  rw [norm_fderiv_gradient hW]
  exact (second_fderiv_norm_le_iterated x).trans (h2.2.2.trans (le_max_right _ _))

end OAI.Analysis.PDE.Elliptic
