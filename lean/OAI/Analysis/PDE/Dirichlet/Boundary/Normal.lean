import OAI.Analysis.PDE.Dirichlet.Boundary.Gradient

open Filter Set
open scoped Topology

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Differentiate the two defining-function barriers in an inward direction. -/
theorem inward_barrier_derivatives {u r : E → ℝ} {x v : E} {b B : ℝ}
    (hu : DifferentiableAt ℝ u x) (hr : DifferentiableAt ℝ r x)
    (hux : u x = 0) (hrx : r x = 0)
    (hcontrol : ∀ᶠ y in 𝓝 x, r y < 0 → B * r y ≤ u y ∧ u y ≤ b * r y)
    (hinward : fderiv ℝ r x v < 0) :
    B * fderiv ℝ r x v ≤ fderiv ℝ u x v ∧
      fderiv ℝ u x v ≤ b * fderiv ℝ r x v := by
  have hline : HasDerivAt (fun t : ℝ ↦ x + t • v) v 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x)
  have hu' : DifferentiableAt ℝ u (x + (0 : ℝ) • v) := by simpa using hu
  have hr' : DifferentiableAt ℝ r (x + (0 : ℝ) • v) := by simpa using hr
  have hDu := hu'.hasFDerivAt.comp_hasDerivAt 0 hline
  have hDr := hr'.hasFDerivAt.comp_hasDerivAt 0 hline
  have htu : Tendsto (fun t : ℝ ↦ u (x + t • v) / t) (𝓝[>] 0)
      (𝓝 (fderiv ℝ u x v)) := by
    simpa [hux, div_eq_inv_mul] using hDu.tendsto_slope_zero_right
  have htr : Tendsto (fun t : ℝ ↦ r (x + t • v) / t) (𝓝[>] 0)
      (𝓝 (fderiv ℝ r x v)) := by
    simpa [hrx, div_eq_inv_mul] using hDr.tendsto_slope_zero_right
  have hpoint : Tendsto (fun t : ℝ ↦ x + t • v) (𝓝[>] 0) (𝓝 x) := by
    simpa using hline.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hneg : ∀ᶠ t : ℝ in 𝓝[>] 0, r (x + t • v) / t < 0 :=
    htr.eventually (eventually_lt_nhds hinward)
  have hle : ∀ᶠ t : ℝ in 𝓝[>] 0,
      B * (r (x + t • v) / t) ≤ u (x + t • v) / t ∧
      u (x + t • v) / t ≤ b * (r (x + t • v) / t) := by
    filter_upwards [hpoint.eventually hcontrol, hneg, self_mem_nhdsWithin] with t hc hn ht
    have htpos : 0 < t := ht
    have hrneg : r (x + t • v) < 0 := by
      simpa using (div_lt_iff₀ htpos).mp hn
    constructor
    · simpa only [mul_div_assoc] using
        div_le_div_of_nonneg_right (hc hrneg).1 htpos.le
    · simpa only [mul_div_assoc] using
        div_le_div_of_nonneg_right (hc hrneg).2 htpos.le
  exact ⟨le_of_tendsto_of_tendsto (tendsto_const_nhds.mul htr) htu (hle.mono fun _ h ↦ h.1),
    le_of_tendsto_of_tendsto htu (tendsto_const_nhds.mul htr) (hle.mono fun _ h ↦ h.2)⟩

theorem linear_form_factor_of_kernel (f g : E →L[ℝ] ℝ) (hg : g ≠ 0)
    (hker : ∀ v, g v = 0 → f v = 0) : ∃ a : ℝ, f = a • g := by
  have he : ∃ w, g w ≠ 0 := by
    by_contra h
    push Not at h
    apply hg
    ext w
    exact h w
  obtain ⟨w, hw⟩ := he
  refine ⟨f w / g w, ?_⟩
  ext v
  have hz : g (v - (g v / g w) • w) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hw, sub_self]
  have hfz := hker _ hz
  simp only [map_sub, map_smul, smul_eq_mul] at hfz
  change f v = (f w / g w) * g v
  calc
    f v = (g v / g w) * f w := sub_eq_zero.mp hfz
    _ = _ := by ring

theorem linear_form_exists_negative (g : E →L[ℝ] ℝ) (hg : g ≠ 0) :
    ∃ w, g w < 0 := by
  have he : ∃ w, g w ≠ 0 := by
    by_contra h
    push Not at h
    apply hg
    ext w
    exact h w
  obtain ⟨w, hw⟩ := he
  by_cases hn : g w < 0
  · exact ⟨w, hn⟩
  · refine ⟨-w, ?_⟩
    simp only [map_neg]
    exact neg_neg_of_pos (lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hw))

/-- At a noncharacteristic boundary point the solution gradient is a positive,
data-bounded multiple of the defining-function gradient. -/
theorem boundary_gradient_factor_of_barriers {u r : E → ℝ} {K : Set E}
    {x : E} {b B : ℝ}
    (hu : DifferentiableAt ℝ u x) (hr : DifferentiableAt ℝ r x)
    (hux : u x = 0) (hrx : r x = 0) (hrne : fderiv ℝ r x ≠ 0)
    (hb : 0 ≤ b) (_ : b ≤ B)
    (hbarriers : ∀ y ∈ K, B * r y ≤ u y ∧ u y ≤ b * r y)
    (hnear : ∀ᶠ y in 𝓝 x, r y < 0 → y ∈ K) :
    ∃ a : ℝ, b ≤ a ∧ a ≤ B ∧ fderiv ℝ u x = a • fderiv ℝ r x := by
  have hcontrol : ∀ᶠ y in 𝓝 x, r y < 0 → B * r y ≤ u y ∧ u y ≤ b * r y := by
    filter_upwards [hnear] with y hy
    exact fun h ↦ hbarriers y (hy h)
  have habs : ∀ᶠ y in 𝓝 x, r y < 0 → |u y| ≤ B * |r y| := by
    filter_upwards [hcontrol] with y hy
    intro hry
    obtain ⟨hl, hu⟩ := hy hry
    have hnonpos : u y ≤ 0 := hu.trans (mul_nonpos_of_nonneg_of_nonpos hb hry.le)
    rw [abs_of_nonpos hnonpos, abs_of_neg hry]
    nlinarith
  have hbound := boundary_derivative_bound hu hr hux hrx hrne habs
  obtain ⟨a, ha⟩ := linear_form_factor_of_kernel (fderiv ℝ u x) (fderiv ℝ r x) hrne
    (fun v hv ↦ by simpa only [hv, abs_zero, mul_zero, abs_nonpos_iff] using hbound v)
  obtain ⟨w, hw⟩ := linear_form_exists_negative (fderiv ℝ r x) hrne
  have hineq := inward_barrier_derivatives hu hr hux hrx hcontrol hw
  simp only [ha, smul_apply, smul_eq_mul] at hineq
  exact ⟨a, (mul_le_mul_right_of_neg hw).mp hineq.2,
    (mul_le_mul_right_of_neg hw).mp hineq.1, ha⟩

end OAI.Analysis.PDE.Dirichlet
