import OAI.Geometry.Nikodym.Beltrami.Geodesic

noncomputable section
namespace OAI.Geometry.Nikodym

open Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem IsBeltramiGeodesic.segment_image
    {κ a b : ℝ} {γ v : ℝ → E} {I : Set ℝ}
    (h : IsBeltramiGeodesic κ γ v I) (hI : IsOpen I) (hconn : IsPreconnected I)
    (hab : a ≤ b) (hsub : Icc a b ⊆ I) (hva : v a ≠ 0) :
    γ '' Icc a b = segment ℝ (γ a) (γ b) := by
  have ha : a ∈ I := hsub (left_mem_Icc.mpr hab)
  have hb : b ∈ I := hsub (right_mem_Icc.mpr hab)
  let c : E := (beltramiDenominator κ (γ a))⁻¹ • v a
  have hc : c ≠ 0 := smul_ne_zero (inv_ne_zero (h.regular a ha).ne') hva
  have hn : ‖c‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hc)
  have hv : ∀ t ∈ I, v t = beltramiDenominator κ (γ t) • c :=
    fun t ht => h.velocity_eq hI hconn ha ht
  let s : ℝ → ℝ := fun t => (⟪c,γ t⟫ - ⟪c,γ a⟫) / ‖c‖^2
  have hs : ∀ t ∈ I, HasDerivAt s (beltramiDenominator κ (γ t)) t := by
    intro t ht
    have hi : HasDerivAt (fun t => ⟪c,γ t⟫) ⟪c,v t⟫ t := by
      simpa using (hasDerivAt_const t c).inner ℝ (h.position_derivative t ht)
    convert (hi.sub_const ⟪c,γ a⟫).div_const (‖c‖^2) using 1
    rw [hv t ht,inner_smul_right,real_inner_self_eq_norm_sq]
    simp [hn]
  have hs₀ : s a = 0 := by simp [s]
  have hpos : ∀ t ∈ I, γ t = γ a + s t • c := by
    let F : ℝ → E := fun t => γ t - s t • c
    have hF : ∀ t ∈ I, HasDerivAt F 0 t := by
      intro t ht
      convert (h.position_derivative t ht).sub ((hs t ht).smul_const c) using 1
      rw [hv t ht,sub_self]
    intro t ht
    have heq : F t = F a := hI.is_const_of_deriv_eq_zero hconn
      (fun t ht => (hF t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (hF t ht).deriv) ht ha
    dsimp [F] at heq
    rw [hs₀,zero_smul,sub_zero] at heq
    exact sub_eq_iff_eq_add.mp heq
  have hsc : ContinuousOn s (Icc a b) :=
    fun t ht => (hs t (hsub ht)).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn s (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b) hsc
    intro t ht
    have htI : t ∈ I := hsub (interior_subset ht)
    rw [(hs t htI).deriv]
    exact h.regular t htI
  have hsab : s a ≤ s b := hmono.monotoneOn (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  have himage : s '' Icc a b = Icc 0 (s b) := by
    simpa only [hs₀] using hsc.image_Icc_of_monotoneOn hab hmono.monotoneOn
  let F : ℝ →ᵃ[ℝ] E := AffineMap.lineMap (γ a) (γ a + c)
  have hF (r : ℝ) : F r = γ a + r • c := by
    simp only [F,AffineMap.lineMap_apply,vsub_eq_sub,vadd_eq_add]
    module
  calc
    γ '' Icc a b = (F ∘ s) '' Icc a b := by
      apply image_congr
      intro t ht
      exact (hpos t (hsub ht)).trans (hF (s t)).symm
    _ = F '' Icc 0 (s b) := by rw [image_comp,himage]
    _ = F '' segment ℝ 0 (s b) := by rw [segment_eq_Icc (by simpa [hs₀] using hsab)]
    _ = segment ℝ (F 0) (F (s b)) := image_segment ℝ F 0 (s b)
    _ = segment ℝ (γ a) (γ b) := by rw [hF,hF,zero_smul,add_zero,← hpos b hb]

end OAI.Geometry.Nikodym
