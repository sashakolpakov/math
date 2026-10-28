import OAI.Geometry.Nikodym.Jacobi.RadialCenter

noncomputable section
namespace OAI.Geometry.Nikodym

open Set Filter Metric
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A genuine smooth projective radial chart through the center. -/
theorem projectiveRadialMap_smooth_local_inverse (κ : ℝ) :
    ∃ (r : ℝ) (G : E → E), 0 < r ∧ G 0 = 0 ∧
      ContDiffOn ℝ ∞ G (ball 0 r) ∧
      (∀ y ∈ ball 0 r, projectiveRadialMap κ (G y) = y) ∧
      (∀ᶠ x in 𝓝 0, G (projectiveRadialMap κ x) = x) := by
  let P : E → E := projectiveRadialMap κ
  have hc : ContDiffAt ℝ ∞ P 0 :=
    contDiffAt_projectiveRadialMap_center_included κ (by simp)
  have hd : HasFDerivAt P (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) 0 :=
    hasFDerivAt_projectiveRadialMap_zero κ
  let e := hc.toOpenPartialHomeomorph P hd (by simp)
  have hsource : (0:E) ∈ e.source := hc.mem_toOpenPartialHomeomorph_source hd (by simp)
  have htarget : (0:E) ∈ e.target := by
    have hh := hc.image_mem_toOpenPartialHomeomorph_target hd (by simp)
    simpa only [P,projectiveRadialMap_zero] using hh
  have hinv : e.symm 0 = 0 := by
    have hh : e.symm (P 0) = 0 := e.left_inv hsource
    simpa only [P,projectiveRadialMap_zero] using hh
  have hD : ContinuousAt (fderiv ℝ P) (0:E) :=
    (hc.fderiv_right (m := 1) (by simp)).continuousAt
  have hgood0 : {x : E | ∃ L : E ≃L[ℝ] E, (L : E →L[ℝ] E) = fderiv ℝ P x} ∈ 𝓝 (0:E) := by
    change (fderiv ℝ P) ⁻¹' {A : E →L[ℝ] E | ∃ L : E ≃L[ℝ] E, (L : E →L[ℝ] E) = A} ∈ 𝓝 (0:E)
    apply hD.preimage_mem_nhds
    rw [hd.fderiv]
    exact (ContinuousLinearEquiv.refl ℝ E).nhds
  have hcos0 : ∀ᶠ x : E in 𝓝 0, curvatureCos κ ‖x‖ ≠ 0 := by
    have hh : ContinuousAt (fun x : E => curvatureCos κ ‖x‖) 0 :=
      (contDiff_curvatureCos κ).continuous.continuousAt.comp continuous_norm.continuousAt
    exact hh.eventually_ne (by simp)
  have hecont : ContinuousAt e.symm (0:E) := e.symm.continuousAt htarget
  have hgood : ∀ᶠ y in 𝓝 (0:E), y ∈ e.target ∧ curvatureCos κ ‖e.symm y‖ ≠ 0 ∧
      ∃ L : E ≃L[ℝ] E, (L : E →L[ℝ] E) = fderiv ℝ P (e.symm y) := by
    have hpair : ∀ᶠ x : E in 𝓝 (e.symm 0), curvatureCos κ ‖x‖ ≠ 0 ∧
        ∃ L : E ≃L[ℝ] E, (L : E →L[ℝ] E) = fderiv ℝ P x := by
      rw [hinv]
      exact Filter.Eventually.and hcos0 hgood0
    have hh := hecont.tendsto.eventually hpair
    exact Filter.Eventually.and (e.open_target.mem_nhds htarget) hh
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hgood
  have hG : ContDiffOn ℝ ∞ e.symm (ball 0 r) := by
    intro y hy
    obtain ⟨hyt,hcy,L,hL⟩ := hball hy
    have hPy : ContDiffAt ℝ ∞ P (e.symm y) :=
      contDiffAt_projectiveRadialMap_center_included κ hcy
    apply ContDiffAt.contDiffWithinAt
    apply e.contDiffAt_symm hyt
    · change HasFDerivAt P (L : E →L[ℝ] E) (e.symm y)
      rw [hL]
      exact (hPy.differentiableAt (by simp)).hasFDerivAt
    · exact hPy
  refine ⟨r,e.symm,hr,hinv,hG,fun y hy => e.right_inv (hball hy).1,?_⟩
  filter_upwards [e.open_source.mem_nhds hsource] with x hx
  exact e.left_inv hx

end OAI.Geometry.Nikodym
