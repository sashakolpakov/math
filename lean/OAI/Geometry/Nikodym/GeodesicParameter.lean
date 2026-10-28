import OAI.Geometry.Nikodym.Beltrami.Segment

noncomputable section
namespace OAI.Geometry.Nikodym

open Set
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A nonconstant Beltrami geodesic is an actual differentiable monotone
reparameterization of its endpoint segment, not merely contained in its line. -/
theorem IsBeltramiGeodesic.monotone_endpoint_parameter
    {κ a b : ℝ} {γ v : ℝ → E} {I : Set ℝ}
    (h : IsBeltramiGeodesic κ γ v I) (hI : IsOpen I) (hconn : IsPreconnected I)
    (hab : a < b) (hsub : Icc a b ⊆ I) (hva : v a ≠ 0) :
    ∃ θ : ℝ → ℝ, θ a = 0 ∧ θ b = 1 ∧ MonotoneOn θ (Icc a b) ∧
      DifferentiableOn ℝ θ (Icc a b) ∧
      EqOn γ (AffineMap.lineMap (γ a) (γ b) ∘ θ) (Icc a b) := by
  have ha : a ∈ I := hsub (left_mem_Icc.mpr hab.le)
  have hb : b ∈ I := hsub (right_mem_Icc.mpr hab.le)
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
  have hsb : 0 < s b := by
    simpa only [hs₀] using hmono (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab
  let θ : ℝ → ℝ := fun t => s t / s b
  refine ⟨θ,by simp [θ,hs₀],by simp [θ,hsb.ne'],?_,?_,?_⟩
  · intro t ht u hu htu
    exact div_le_div_of_nonneg_right (hmono.monotoneOn ht hu htu) hsb.le
  · intro t ht
    exact ((hs t (hsub ht)).div_const (s b)).differentiableAt.differentiableWithinAt
  · intro t ht
    change γ t = AffineMap.lineMap (γ a) (γ b) (s t / s b)
    rw [AffineMap.lineMap_apply_module,hpos b hb]
    have hcancel : (s t / s b) * s b = s t := div_mul_cancel₀ _ hsb.ne'
    rw [smul_add,smul_smul,hcancel,← add_assoc,← add_smul]
    simp only [sub_add_cancel,one_smul]
    exact hpos t (hsub ht)

theorem IsBeltramiGeodesic.constant_of_zero_velocity
    {κ a : ℝ} {γ v : ℝ → E} {I : Set ℝ}
    (h : IsBeltramiGeodesic κ γ v I) (hI : IsOpen I) (hconn : IsPreconnected I)
    (ha : a ∈ I) (hva : v a = 0) : ∀ t ∈ I, γ t = γ a := by
  have hv : ∀ t ∈ I, v t = 0 := by
    intro t ht
    rw [h.velocity_eq hI hconn ha ht,hva,smul_zero,smul_zero]
  intro t ht
  exact hI.is_const_of_deriv_eq_zero hconn
    (fun s hs => (h.position_derivative s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (h.position_derivative s hs).deriv.trans (hv s hs)) ht ha

theorem IsBeltramiGeodesic.segment_image_of_le
    {κ a b : ℝ} {γ v : ℝ → E} {I : Set ℝ}
    (h : IsBeltramiGeodesic κ γ v I) (hI : IsOpen I) (hconn : IsPreconnected I)
    (hab : a ≤ b) (hsub : Icc a b ⊆ I) :
    γ '' Icc a b = segment ℝ (γ a) (γ b) := by
  by_cases hv : v a = 0
  · have hc := h.constant_of_zero_velocity hI hconn
      (hsub (left_mem_Icc.mpr hab)) hv
    have he : γ '' Icc a b = {γ a} := by
      ext x
      constructor
      · rintro ⟨t,ht,rfl⟩
        exact hc t (hsub ht)
      · intro hx
        exact ⟨a,left_mem_Icc.mpr hab,hx.symm⟩
    rw [he,hc b (hsub (right_mem_Icc.mpr hab))]
    simp
  · exact h.segment_image hI hconn hab hsub hv

end OAI.Geometry.Nikodym
