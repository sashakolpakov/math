import OAI.Geometry.Nikodym.Beltrami.Segment
import OAI.Geometry.Nikodym.Beltrami.Length
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
namespace OAI.Geometry.Nikodym

open Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A genuine Beltrami geodesic cannot reverse direction. Consequently,
two-sided speed bounds give the same bounds on its endpoint separation. -/
theorem IsBeltramiGeodesic.endpoint_dist_bounds
    {κ a b m M : ℝ} {γ v : ℝ → E} {I : Set ℝ}
    (h : IsBeltramiGeodesic κ γ v I) (hI : IsOpen I) (hconn : IsPreconnected I)
    (hab : a ≤ b) (hsub : Icc a b ⊆ I) (hm : 0 < m)
    (hspeed : ∀ t ∈ Icc a b, m ≤ ‖v t‖ ∧ ‖v t‖ ≤ M) :
    m * (b-a) ≤ dist (γ a) (γ b) ∧ dist (γ a) (γ b) ≤ M * (b-a) := by
  have ha : a ∈ I := hsub (left_mem_Icc.mpr hab)
  have hb : b ∈ I := hsub (right_mem_Icc.mpr hab)
  have hva : v a ≠ 0 := by
    intro he
    have hh := (hspeed a (left_mem_Icc.mpr hab)).1
    simp only [he,norm_zero] at hh
    exact hm.not_ge hh
  let c : E := (beltramiDenominator κ (γ a))⁻¹ • v a
  have hc : c ≠ 0 := smul_ne_zero (inv_ne_zero (h.regular a ha).ne') hva
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hv : ∀ t ∈ I, v t = beltramiDenominator κ (γ t) • c :=
    fun t ht => h.velocity_eq hI hconn ha ht
  let s : ℝ → ℝ := fun t => ⟪c,γ t⟫ / ‖c‖
  have hs : ∀ t ∈ I, HasDerivAt s ‖v t‖ t := by
    intro t ht
    have hi : HasDerivAt (fun t => ⟪c,γ t⟫) ⟪c,v t⟫ t := by
      simpa using (hasDerivAt_const t c).inner ℝ (h.position_derivative t ht)
    have heq : ⟪c,v t⟫ / ‖c‖ = ‖v t‖ := by
      rw [hv t ht,inner_smul_right,real_inner_self_eq_norm_sq]
      conv_rhs => rw [norm_smul,Real.norm_eq_abs,abs_of_pos (h.regular t ht)]
      field_simp [hcpos.ne']
    simpa only [heq] using hi.div_const ‖c‖
  have hcont : ContinuousOn s (Icc a b) :=
    fun t ht => (hs t (hsub ht)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ s (interior (Icc a b)) :=
    fun t ht => (hs t (hsub (interior_subset ht))).differentiableAt.differentiableWithinAt
  have hder : ∀ t ∈ interior (Icc a b), m ≤ deriv s t := by
    intro t ht
    rw [(hs t (hsub (interior_subset ht))).deriv]
    exact (hspeed t (interior_subset ht)).1
  have hlower : m * (b-a) ≤ s b-s a :=
    (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv hcont hdiff hder
      a (left_mem_Icc.mpr hab) b (right_mem_Icc.mpr hab) hab
  have hproj : s b-s a ≤ ‖γ b-γ a‖ := by
    have heq : s b-s a = ⟪c,γ b-γ a⟫ / ‖c‖ := by
      dsimp [s]
      rw [inner_sub_right]
      ring
    rw [heq,div_le_iff₀ hcpos]
    exact (real_inner_le_norm c (γ b-γ a)).trans_eq (mul_comm _ _)
  have hupper : ‖γ b-γ a‖ ≤ M * (b-a) :=
    norm_image_sub_le_of_norm_deriv_le_segment'
      (fun t ht => (h.position_derivative t (hsub ht)).hasDerivWithinAt)
      (fun t ht => (hspeed t (Ico_subset_Icc_self ht)).2)
      b (right_mem_Icc.mpr hab)
  simpa only [dist_eq_norm, norm_sub_rev] using And.intro (hlower.trans hproj) hupper

/-- Unit metric speed in a small Beltrami chart gives a genuine Euclidean
segment with quantitative length bounds. -/
theorem IsBeltramiGeodesic.unitSpeed_segment_bounds
    {κ a b : ℝ} {γ v : ℝ → E} {I : Set ℝ}
    (h : IsBeltramiGeodesic κ γ v I) (hI : IsOpen I) (hconn : IsPreconnected I)
    (hab : a ≤ b) (hsub : Icc a b ⊆ I)
    (hsmall : ∀ t ∈ Icc a b, |κ| * ‖γ t‖^2 ≤ 1/2)
    (hunit : ∀ t ∈ Icc a b, beltramiMetric κ (γ t) (v t) (v t) = 1) :
    γ '' Icc a b = segment ℝ (γ a) (γ b) ∧
      (b-a)/3 ≤ dist (γ a) (γ b) ∧ dist (γ a) (γ b) ≤ 4*(b-a) := by
  have hs : ∀ t ∈ Icc a b, (1/3 : ℝ) ≤ ‖v t‖ ∧ ‖v t‖ ≤ 4 := by
    intro t ht
    obtain ⟨hl,hu⟩ := beltramiSpeed_small_bounds (hsmall t ht) (v t)
    have heq : beltramiSpeed κ (γ t) (v t) = 1 := by
      simp only [beltramiSpeed,hunit t ht,Real.sqrt_one]
    rw [heq] at hl hu
    constructor <;> linarith
  have hva : v a ≠ 0 := by
    intro heq
    have hl := (hs a (left_mem_Icc.mpr hab)).1
    rw [heq,norm_zero] at hl
    norm_num at hl
  refine ⟨h.segment_image hI hconn hab hsub hva,?_⟩
  have hb := h.endpoint_dist_bounds hI hconn hab hsub (by norm_num : (0:ℝ)<1/3) hs
  simpa only [one_div_mul_eq_div] using hb

end OAI.Geometry.Nikodym
