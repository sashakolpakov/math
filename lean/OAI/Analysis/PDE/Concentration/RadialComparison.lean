import OAI.Analysis.PDE.Concentration.RadialBarrier
import OAI.Analysis.PDE.Concentration.LocalLaplacian
import OAI.Analysis.PDE.Dirichlet.Maximum

namespace OAI.Analysis.PDE.Concentration

open Set Filter
open scoped Topology ContDiff

noncomputable def radialHelmholtz (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv (deriv f) r + deriv f r / r - f r / 100

/-- The zeroth-order term gives a strict one-dimensional maximum principle,
without imposing a global smooth extension across the interval endpoints. -/
theorem radialHelmholtz_maximum {f : ℝ → ℝ} {a b : ℝ} (_ : a < b)
    (hct : ContinuousOn f (Icc a b)) (hf : ContDiffOn ℝ 2 f (Ioo a b))
    (hL : ∀ r ∈ Ioo a b, 0 ≤ radialHelmholtz f r) (ha : f a ≤ 0) (hb : f b ≤ 0) :
    ∀ r ∈ Icc a b, f r ≤ 0 := by
  intro r hr
  obtain ⟨z, hz, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨r, hr⟩ hct
  by_cases hzi : z ∈ Ioo a b
  · have hlocal : IsLocalMax f z := hmax.isLocalMax
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hzi) Ioo_subset_Icc_self)
    obtain ⟨F, V, hF, hV, hzV, _, hEq⟩ :=
      exists_global_contDiff_two_eq_near isOpen_Ioo hf hzi
    have he : F =ᶠ[nhds z] f := eventuallyEq_of_mem (hV.mem_nhds hzV) hEq
    have hlocalF : IsLocalMax F z := by
      filter_upwards [he, hlocal] with y hy hfy
      rw [hy, he.self_of_nhds]
      exact hfy
    have hdd : deriv (deriv f) z ≤ 0 := by
      rw [← he.deriv.deriv_eq]
      exact OAI.Analysis.PDE.Dirichlet.second_deriv_nonpos_of_localMax hF hlocalF
    have hfirst : deriv f z = 0 := hlocal.deriv_eq_zero
    have hh := hL z hzi
    dsimp [radialHelmholtz] at hh
    rw [hfirst, zero_div, add_zero] at hh
    exact (hmax hr).trans (by linarith)
  · have hze : z = a ∨ z = b := by
      rcases hz with ⟨hza, hzb⟩
      simp only [mem_Ioo, not_and_or, not_lt] at hzi
      rcases hzi with h | h
      · exact Or.inl (le_antisymm h hza)
      · exact Or.inr (le_antisymm hzb h)
    exact (hmax hr).trans (hze.elim (fun h => h ▸ ha) (fun h => h ▸ hb))

theorem radialHelmholtz_sub {f g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (hg : ContDiffOn ℝ 2 g U) {r : ℝ} (hr : r ∈ U) :
    radialHelmholtz (fun x => f x - g x) r = radialHelmholtz f r - radialHelmholtz g r := by
  have hfd (x : ℝ) (hx : x ∈ U) : DifferentiableAt ℝ f x :=
    ((hf x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hgd (x : ℝ) (hx : x ∈ U) : DifferentiableAt ℝ g x :=
    ((hg x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have he : deriv (fun x => f x - g x) =ᶠ[nhds r] (fun x => deriv f x - deriv g x) := by
    filter_upwards [hU.mem_nhds hr] with x hx
    exact deriv_fun_sub (hfd x hx) (hgd x hx)
  have hdf : ContDiffOn ℝ 1 (deriv f) U := hf.deriv_of_isOpen hU (by norm_num)
  have hdg : ContDiffOn ℝ 1 (deriv g) U := hg.deriv_of_isOpen hU (by norm_num)
  have hdfd : DifferentiableAt ℝ (deriv f) r :=
    ((hdf r hr).contDiffAt (hU.mem_nhds hr)).differentiableAt (by norm_num)
  have hdgd : DifferentiableAt ℝ (deriv g) r :=
    ((hdg r hr).contDiffAt (hU.mem_nhds hr)).differentiableAt (by norm_num)
  dsimp [radialHelmholtz]
  rw [he.deriv_eq, he.self_of_nhds, deriv_fun_sub hdfd hdgd]
  ring

theorem radialHelmholtz_const_mul {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (c : ℝ) {r : ℝ} (hr : r ∈ U) :
    radialHelmholtz (fun x => c * f x) r = c * radialHelmholtz f r := by
  have hfd (x : ℝ) (hx : x ∈ U) : DifferentiableAt ℝ f x :=
    ((hf x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have he : deriv (fun x => c * f x) =ᶠ[nhds r] (fun x => c * deriv f x) := by
    filter_upwards [hU.mem_nhds hr] with x hx
    exact deriv_const_mul c (hfd x hx)
  have hdf : ContDiffOn ℝ 1 (deriv f) U := hf.deriv_of_isOpen hU (by norm_num)
  have hdfd : DifferentiableAt ℝ (deriv f) r :=
    ((hdf r hr).contDiffAt (hU.mem_nhds hr)).differentiableAt (by norm_num)
  dsimp [radialHelmholtz]
  rw [he.deriv_eq, he.self_of_nhds, deriv_const_mul c hdfd]
  ring

theorem radialHelmholtz_comparison {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfct : ContinuousOn f (Icc a b)) (hgct : ContinuousOn g (Icc a b))
    (hf : ContDiffOn ℝ 2 f (Ioo a b)) (hg : ContDiffOn ℝ 2 g (Ioo a b))
    (hL : ∀ r ∈ Ioo a b, radialHelmholtz g r ≤ radialHelmholtz f r)
    (ha : f a ≤ g a) (hb : f b ≤ g b) : ∀ r ∈ Icc a b, f r ≤ g r := by
  have hh := radialHelmholtz_maximum hab (hfct.sub hgct) (hf.sub hg)
    (fun r hr => by
      change 0 ≤ radialHelmholtz (fun x => f x - g x) r
      rw [radialHelmholtz_sub isOpen_Ioo hf hg hr]
      exact sub_nonneg.mpr (hL r hr))
    (sub_nonpos.mpr ha) (sub_nonpos.mpr hb)
  intro r hr
  exact sub_nonpos.mp (hh r hr)

/-- A nonnegative radial supersolution propagates the inner boundary value
to every fixed outer radius with only a logarithmic loss. -/
theorem radialHelmholtz_logarithmic_lower {H : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a) (ha3 : a < 3) (hct : ContinuousOn H (Icc a 3))
    (hH : ContDiffOn ℝ 2 H (Ioo a 3))
    (hL : ∀ r ∈ Ioo a 3, radialHelmholtz H r ≤ 0)
    (hHa : 0 ≤ H a) (hH3 : 0 ≤ H 3) :
    ∀ r ∈ Icc a 3,
      H a / cylinderRadialBarrier a * cylinderRadialBarrier r ≤ H r := by
  let c := H a / cylinderRadialBarrier a
  have hRpos := cylinderRadialBarrier_pos ha ha3
  have hc : 0 ≤ c := div_nonneg hHa hRpos.le
  have hsub : Icc a 3 ⊆ Ioi 0 := fun r hr => ha.trans_le hr.1
  have hRc : ContinuousOn cylinderRadialBarrier (Icc a 3) :=
    contDiffOn_cylinderRadialBarrier.continuousOn.mono hsub
  have hRd : ContDiffOn ℝ 2 cylinderRadialBarrier (Ioo a 3) :=
    contDiffOn_cylinderRadialBarrier.mono (Ioo_subset_Icc_self.trans hsub)
  apply radialHelmholtz_comparison ha3 (continuousOn_const.mul hRc) hct
    (contDiffOn_const.mul hRd) hH
  · intro r hr
    change radialHelmholtz H r ≤ radialHelmholtz (fun x => c * cylinderRadialBarrier x) r
    rw [radialHelmholtz_const_mul isOpen_Ioo hRd c hr]
    apply (hL r hr).trans
    apply mul_nonneg hc
    exact sub_nonneg.mpr (cylinderRadialBarrier_subsolution (ha.trans hr.1) hr.2.le)
  · change c * cylinderRadialBarrier a ≤ H a
    dsimp [c]
    rw [div_mul_cancel₀ _ hRpos.ne']
  · change c * cylinderRadialBarrier 3 ≤ H 3
    simpa only [cylinderRadialBarrier_three, mul_zero] using hH3

theorem radialHelmholtz_unit_lower {H : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hct : ContinuousOn H (Icc a 3))
    (hH : ContDiffOn ℝ 2 H (Ioo a 3))
    (hL : ∀ r ∈ Ioo a 3, radialHelmholtz H r ≤ 0)
    (hHa : 0 ≤ H a) (hH3 : 0 ≤ H 3) :
    H a * (Real.log 3 / (4 * (Real.log 3 - Real.log a))) ≤ H 1 := by
  have ha3 : a < 3 := by linarith
  have hb := radialHelmholtz_logarithmic_lower ha ha3 hct hH hL hHa hH3 1
    ⟨ha1.le, by norm_num⟩
  have hRa := cylinderRadialBarrier_pos ha ha3
  have hR1 := cylinderRadialBarrier_pos (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 3)
  have hlog : 0 < Real.log 3 - Real.log a := sub_pos.mpr (Real.log_lt_log ha ha3)
  have hlow : Real.log 3 / 2 ≤ cylinderRadialBarrier 1 := by
    simpa using (cylinderRadialBarrier_bounds (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (1 : ℝ) ≤ 3)).1
  have hupper := (cylinderRadialBarrier_bounds ha ha3.le).2
  apply le_trans _ hb
  calc
    _ = H a * ((Real.log 3 / 2) / (2 * (Real.log 3 - Real.log a))) := by
      field_simp
      ; ring
    _ ≤ H a * (cylinderRadialBarrier 1 / cylinderRadialBarrier a) := by
      apply mul_le_mul_of_nonneg_left _ hHa
      exact div_le_div₀ (by positivity) hlow hRa hupper
    _ = _ := by ring

end OAI.Analysis.PDE.Concentration
