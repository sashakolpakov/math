import OAI.Geometry.Nikodym.Jacobi.Projective

noncomputable section
namespace OAI.Geometry.Nikodym

open Set Filter Metric
open scoped Topology ContDiff

theorem curvatureTan_inverse_derivative {κ s : ℝ} {G : ℝ → ℝ}
    (hG : ContinuousAt G s) (hc : curvatureCos κ (G s) ≠ 0)
    (hi : ∀ᶠ x in 𝓝 s, curvatureTan κ (G x) = x) :
    HasDerivAt G (1 / (1 + κ*s^2)) s := by
  have hd := (hasDerivAt_curvatureTan κ (G s) hc).of_local_left_inverse hG
    (one_div_ne_zero (pow_ne_zero 2 hc)) hi
  have he := curvatureTan_denominator κ (G s) hc
  rw [hi.self_of_nhds] at he
  simpa only [← he,one_div] using! hd

/-- The projective radial coordinate has a genuine smooth local inverse.
The inverse is constructed by the inverse function theorem; no model-chart
or local-invertibility hypothesis is assumed. -/
theorem curvatureTan_smooth_local_inverse (κ : ℝ) :
    ∃ (r : ℝ) (G : ℝ → ℝ), 0 < r ∧ G 0 = 0 ∧
      ContDiffOn ℝ ∞ G (ball 0 r) ∧
      (∀ s ∈ ball 0 r, curvatureTan κ (G s) = s ∧ 0 < curvatureCos κ (G s)) ∧
      (∀ᶠ t in 𝓝 0, G (curvatureTan κ t) = t) := by
  have hc : ContDiffAt ℝ ∞ (curvatureTan κ) 0 :=
    contDiffAt_curvatureTan κ 0 (by simp)
  have hd : HasFDerivAt (curvatureTan κ)
      (ContinuousLinearEquiv.refl ℝ ℝ : ℝ →L[ℝ] ℝ) 0 := by
    have hd0 : HasDerivAt (curvatureTan κ) 1 0 := by
      simpa using! hasDerivAt_curvatureTan κ 0 (by simp)
    convert hd0.hasFDerivAt using 1
    ext
    simp
  let e := hc.toOpenPartialHomeomorph (curvatureTan κ) hd (by simp)
  have he0 : (0:ℝ) ∈ e.source := hc.mem_toOpenPartialHomeomorph_source hd (by simp)
  have het : (0:ℝ) ∈ e.target := by
    simpa only [curvatureTan_zero] using hc.image_mem_toOpenPartialHomeomorph_target hd (by simp)
  have hei : e.symm 0 = 0 := by
    have hh : e.symm (curvatureTan κ 0) = 0 := e.left_inv he0
    simpa only [curvatureTan_zero] using hh
  have hecont : ContinuousAt e.symm 0 := e.symm.continuousAt het
  have hpos : ∀ᶠ s in 𝓝 (0:ℝ), 0 < curvatureCos κ (e.symm s) := by
    have hcc := (contDiff_curvatureCos κ).continuous.continuousAt.comp hecont
    exact hcc.eventually (lt_mem_nhds (by simp [hei]))
  have hgood := Filter.Eventually.and (e.open_target.mem_nhds het) hpos
  obtain ⟨r,hr,hrgood⟩ := Metric.mem_nhds_iff.mp hgood
  have hGsmooth : ContDiffOn ℝ ∞ e.symm (ball 0 r) := by
    intro s hs
    obtain ⟨hst,hsp⟩ := hrgood hs
    let d : ℝ := 1 / (curvatureCos κ (e.symm s))^2
    have hdpos : 0 < d := div_pos zero_lt_one (sq_pos_of_pos hsp)
    let L : ℝ ≃L[ℝ] ℝ := (LinearEquiv.smulOfNeZero ℝ ℝ d hdpos.ne').toContinuousLinearEquiv
    have hL : (L : ℝ →L[ℝ] ℝ) = ContinuousLinearMap.toSpanSingleton ℝ d := by
      ext
      simp [L,smul_eq_mul,mul_comm]
    apply ContDiffAt.contDiffWithinAt
    apply e.contDiffAt_symm hst
    · change HasFDerivAt (curvatureTan κ) (L : ℝ →L[ℝ] ℝ) (e.symm s)
      rw [hL]
      exact (hasDerivAt_curvatureTan κ (e.symm s) hsp.ne').hasFDerivAt
    · exact contDiffAt_curvatureTan κ (e.symm s) hsp.ne'
  refine ⟨r,e.symm,hr,hei,hGsmooth,?_,?_⟩
  · intro s hs
    exact ⟨e.right_inv (hrgood hs).1,(hrgood hs).2⟩
  · filter_upwards [e.open_source.mem_nhds he0] with t ht
    exact e.left_inv ht

end OAI.Geometry.Nikodym
