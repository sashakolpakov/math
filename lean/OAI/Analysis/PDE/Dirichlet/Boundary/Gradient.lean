import OAI.Analysis.PDE.Dirichlet.CoerciveData
import Mathlib.Analysis.Calculus.Deriv.Slope

open Filter Set
open scoped Topology

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

section NormedSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A one-sided defining-function bound controls every inward derivative. -/
theorem inward_derivative_bound {u r : E → ℝ} {x v : E} {C : ℝ}
    (hu : DifferentiableAt ℝ u x) (hr : DifferentiableAt ℝ r x)
    (hux : u x = 0) (hrx : r x = 0)
    (hcontrol : ∀ᶠ y in 𝓝 x, r y < 0 → |u y| ≤ C * |r y|)
    (hinward : fderiv ℝ r x v < 0) :
    |fderiv ℝ u x v| ≤ C * |fderiv ℝ r x v| := by
  have hline : HasDerivAt (fun t : ℝ ↦ x + t • v) v 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x)
  have hu' : DifferentiableAt ℝ u (x + (0 : ℝ) • v) := by simpa using hu
  have hr' : DifferentiableAt ℝ r (x + (0 : ℝ) • v) := by simpa using hr
  have hDu := hu'.hasFDerivAt.comp_hasDerivAt 0 hline
  have hDr := hr'.hasFDerivAt.comp_hasDerivAt 0 hline
  have htu : Tendsto (fun t : ℝ ↦ u (x + t • v) / t) (𝓝[>] 0) (𝓝 (fderiv ℝ u x v)) := by
    simpa [hux, div_eq_inv_mul] using hDu.tendsto_slope_zero_right
  have htr : Tendsto (fun t : ℝ ↦ r (x + t • v) / t) (𝓝[>] 0) (𝓝 (fderiv ℝ r x v)) := by
    simpa [hrx, div_eq_inv_mul] using hDr.tendsto_slope_zero_right
  have hpoint : Tendsto (fun t : ℝ ↦ x + t • v) (𝓝[>] 0) (𝓝 x) := by
    simpa using hline.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hneg : ∀ᶠ t : ℝ in 𝓝[>] 0, r (x + t • v) / t < 0 :=
    htr.eventually (eventually_lt_nhds hinward)
  have hle : ∀ᶠ t : ℝ in 𝓝[>] 0,
      |u (x + t • v) / t| ≤ C * |r (x + t • v) / t| := by
    filter_upwards [hpoint.eventually hcontrol, hneg, self_mem_nhdsWithin] with t hc hn ht
    have htpos : 0 < t := ht
    have hrneg : r (x + t • v) < 0 := by
      simpa using (div_lt_iff₀ htpos).mp hn
    have hb := div_le_div_of_nonneg_right (hc hrneg) htpos.le
    simpa only [abs_div, abs_of_pos htpos, mul_div_assoc] using hb
  exact le_of_tendsto_of_tendsto htu.abs (tendsto_const_nhds.mul htr.abs) hle

/-- Control on an open half-space extends to its tangent hyperplane. -/
theorem linear_form_bound_of_halfspace (f g : E →L[ℝ] ℝ) (hg : g ≠ 0) (C : ℝ)
    (hbound : ∀ v, g v < 0 → |f v| ≤ C * |g v|) :
    ∀ v, |f v| ≤ C * |g v| := by
  have hw : ∃ w, g w < 0 := by
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
  obtain ⟨w, hw⟩ := hw
  intro v
  by_cases hn : g v < 0
  · exact hbound v hn
  by_cases hp : 0 < g v
  · simpa only [map_neg, abs_neg] using hbound (-v) (by simpa using neg_neg_of_pos hp)
  have hz : g v = 0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
  have hε : ∀ᶠ ε : ℝ in 𝓝[>] 0, |f (v + ε • w)| ≤ C * |g (v + ε • w)| := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    apply hbound
    simp only [map_add, map_smul, smul_eq_mul, hz, zero_add]
    exact mul_neg_of_pos_of_neg hε hw
  have hfT : Tendsto (fun ε : ℝ ↦ |f (v + ε • w)|) (𝓝[>] 0) (𝓝 |f v|) := by
    have hc : Continuous (fun ε : ℝ ↦ |f (v + ε • w)|) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hgT : Tendsto (fun ε : ℝ ↦ C * |g (v + ε • w)|) (𝓝[>] 0) (𝓝 (C * |g v|)) := by
    have hc : Continuous (fun ε : ℝ ↦ C * |g (v + ε • w)|) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact le_of_tendsto_of_tendsto hfT hgT hε

theorem boundary_derivative_bound {u r : E → ℝ} {x : E} {C : ℝ}
    (hu : DifferentiableAt ℝ u x) (hr : DifferentiableAt ℝ r x)
    (hux : u x = 0) (hrx : r x = 0) (hrne : fderiv ℝ r x ≠ 0)
    (hcontrol : ∀ᶠ y in 𝓝 x, r y < 0 → |u y| ≤ C * |r y|) :
    ∀ v, |fderiv ℝ u x v| ≤ C * |fderiv ℝ r x v| := by
  apply linear_form_bound_of_halfspace _ _ hrne C
  intro v hv
  exact inward_derivative_bound hu hr hux hrx hcontrol hv

theorem boundary_gradient_norm_bound {u r : E → ℝ} {x : E} {C : ℝ}
    (hu : DifferentiableAt ℝ u x) (hr : DifferentiableAt ℝ r x)
    (hux : u x = 0) (hrx : r x = 0) (hrne : fderiv ℝ r x ≠ 0) (hC : 0 ≤ C)
    (hcontrol : ∀ᶠ y in 𝓝 x, r y < 0 → |u y| ≤ C * |r y|) :
    ‖fderiv ℝ u x‖ ≤ C * ‖fderiv ℝ r x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg _))
  intro v
  calc
    ‖fderiv ℝ u x v‖ ≤ C * ‖fderiv ℝ r x v‖ := by
      simpa only [Real.norm_eq_abs] using boundary_derivative_bound hu hr hux hrx hrne hcontrol v
    _ ≤ C * (‖fderiv ℝ r x‖ * ‖v‖) := mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) hC
    _ = _ := by ring

theorem boundary_gradient_norm_of_barriers {u r : E → ℝ} {K : Set E} {x : E} {b B : ℝ}
    (hu : DifferentiableAt ℝ u x) (hr : DifferentiableAt ℝ r x)
    (hux : u x = 0) (hrx : r x = 0) (hrne : fderiv ℝ r x ≠ 0)
    (hb : 0 ≤ b) (hbB : b ≤ B)
    (hbarriers : ∀ y ∈ K, B * r y ≤ u y ∧ u y ≤ b * r y)
    (hnear : ∀ᶠ y in 𝓝 x, r y < 0 → y ∈ K) :
    ‖fderiv ℝ u x‖ ≤ B * ‖fderiv ℝ r x‖ := by
  apply boundary_gradient_norm_bound hu hr hux hrx hrne (hb.trans hbB)
  filter_upwards [hnear] with y hy
  intro hry
  obtain ⟨hl, hu⟩ := hbarriers y (hy hry)
  have hnonpos : u y ≤ 0 := hu.trans (mul_nonpos_of_nonneg_of_nonpos hb hry.le)
  rw [abs_of_nonpos hnonpos, abs_of_neg hry]
  nlinarith

theorem boundary_gradient_norm_add_of_barriers {f u r : E → ℝ}
    {K : Set E} {x : E} {b B : ℝ}
    (hf : DifferentiableAt ℝ f x) (hu : DifferentiableAt ℝ u x) (hr : DifferentiableAt ℝ r x)
    (hux : u x = 0) (hrx : r x = 0) (hrne : fderiv ℝ r x ≠ 0)
    (hb : 0 ≤ b) (hbB : b ≤ B)
    (hbarriers : ∀ y ∈ K, B * r y ≤ u y ∧ u y ≤ b * r y)
    (hnear : ∀ᶠ y in 𝓝 x, r y < 0 → y ∈ K) :
    ‖fderiv ℝ (fun y ↦ f y + u y) x‖ ≤ ‖fderiv ℝ f x‖ + B * ‖fderiv ℝ r x‖ := by
  have hd : fderiv ℝ (fun y ↦ f y + u y) x = fderiv ℝ f x + fderiv ℝ u x :=
    (hf.hasFDerivAt.add hu.hasFDerivAt).fderiv
  rw [hd]
  exact (norm_add_le _ _).trans (add_le_add le_rfl
    (boundary_gradient_norm_of_barriers hu hr hux hrx hrne hb hbB hbarriers hnear))

end NormedSpace
end OAI.Analysis.PDE.Dirichlet
