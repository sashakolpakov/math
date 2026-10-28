import OAI.Geometry.Nikodym.Beltrami.Length

noncomputable section
namespace OAI.Geometry.Nikodym

open Set _root_.MeasureTheory
open scoped ENNReal ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The intrinsic Riemannian length distance in a Beltrami coordinate
domain: the infimum of the actual metric lengths of all C¹ joining paths. -/
def beltramiChartEDist (κ : ℝ) (S : Set E) (x y : E) : ℝ≥0∞ :=
  ⨅ (γ : ℝ → E) (_ : ContDiffOn ℝ 1 γ (Icc 0 1))
    (_ : γ 0 = x) (_ : γ 1 = y) (_ : MapsTo γ (Icc 0 1) S),
      beltramiPathLength κ γ (deriv γ) 0 1

omit [CompleteSpace E] in
theorem beltramiChartEDist_lower {κ : ℝ} {S : Set E}
    (hsmall : ∀ z ∈ S, |κ| * ‖z‖^2 ≤ 1/2) (x y : E) :
    (1/4 : ℝ≥0∞) * edist x y ≤ beltramiChartEDist κ S x y := by
  unfold beltramiChartEDist
  refine le_iInf fun γ => le_iInf fun hγ => le_iInf fun hx => le_iInf fun hy => le_iInf fun hmap => ?_
  have hlen := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hγ (by norm_num : (0 : ℝ) ≤ 1)
  have hbound := (beltramiPathLength_small_bounds (fun t ht => hsmall _ (hmap ht))
    (v := deriv γ)).1
  have hh := (mul_le_mul' (le_refl (1/4 : ℝ≥0∞)) hlen).trans hbound
  rw [edist_comm x y,edist_eq_enorm_sub]
  simpa [hx,hy] using hh

omit [CompleteSpace E] in
theorem beltramiChartEDist_upper {κ : ℝ} {S : Set E}
    (hsmall : ∀ z ∈ S, |κ| * ‖z‖^2 ≤ 1/2) (hS : Convex ℝ S)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) :
    beltramiChartEDist κ S x y ≤ 3 * edist x y := by
  let γ : ℝ → E := fun t => (1-t) • x + t • y
  have hγ : ContDiff ℝ 1 γ := by unfold γ; fun_prop
  have hmap : MapsTo γ (Icc 0 1) S := by
    intro t ht
    exact hS hx hy (by linarith [ht.2]) ht.1 (by ring)
  have hdγ : ∀ t, deriv γ t = y-x := by
    intro t
    have hd : HasDerivAt γ (-(1 : ℝ) • x + (1 : ℝ) • y) t := by
      convert (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).smul_const x).add
          ((hasDerivAt_id t).smul_const y) using 1 <;>
        simp only [γ,Pi.sub_apply,id_eq,zero_sub]
      rfl
    simpa [sub_eq_add_neg,add_comm] using hd.deriv
  have hlen : beltramiChartEDist κ S x y ≤ beltramiPathLength κ γ (deriv γ) 0 1 := by
    apply iInf_le_of_le γ
    apply iInf_le_of_le hγ.contDiffOn
    apply iInf_le_of_le (by simp [γ] : γ 0 = x)
    apply iInf_le_of_le (by simp [γ] : γ 1 = y)
    exact iInf_le _ hmap
  apply hlen.trans
  have hbound := (beltramiPathLength_small_bounds (fun t ht => hsmall _ (hmap ht))
    (v := deriv γ)).2
  rw [edist_comm x y,edist_eq_enorm_sub]
  simpa [hdγ,Real.volume_Icc] using hbound

end OAI.Geometry.Nikodym
