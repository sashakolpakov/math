import Mathlib

/-! # Analytic Countable Selection -/

namespace OAI.RepresentationTheory.Theta.Geometric.AnalyticCountableSelection

noncomputable section

section

/-! On a connected open complex domain, a holomorphic map that equals
one of countably many holomorphic maps pointwise equals one of them globally. -/

theorem analytic_countable_selection
    {E F I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [BaireSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [Countable I]
    {U : Set E} (hU : IsOpen U) (hc : IsPreconnected U) (hne : U.Nonempty)
    {f : E → F} {g : I → E → F}
    (hf : AnalyticOnNhd ℂ f U) (hg : ∀ i, AnalyticOnNhd ℂ (g i) U)
    (hcover : ∀ x ∈ U, ∃ i, f x = g i x) : ∃ i, Set.EqOn f (g i) U := by
  let : BaireSpace U := hU.baireSpace
  let : Nonempty U := hne.to_subtype
  let Z : I → Set U := fun i => {x | f x.val = g i x.val}
  have hZ (i : I) : IsClosed (Z i) :=
    isClosed_eq (continuousOn_iff_continuous_domRestrict.mp hf.continuousOn)
      (continuousOn_iff_continuous_domRestrict.mp (hg i).continuousOn)
  have hZU : ⋃ i, Z i = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact hcover x.val x.property
  obtain ⟨i, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hZ hZU
  refine ⟨i, hf.eqOn_of_preconnected_of_eventuallyEq (hg i) hc x.property ?_⟩
  have hV : IsOpen ((Subtype.val : U → E) '' interior (Z i)) := hU.isOpenMap_subtype_val _ isOpen_interior
  have hxV : x.val ∈ ((Subtype.val : U → E) '' interior (Z i)) := ⟨x, hx, rfl⟩
  filter_upwards [hV.mem_nhds hxV] with y hy
  obtain ⟨z, hz, rfl⟩ := hy
  exact (show z ∈ Z i from interior_subset hz)

end

/-! A three-by-three complex matrix fixing every projective line in
an open affine chart is scalar; the proof uses holomorphic identity. -/

open Set Filter
open scoped _root_.Topology

def projectiveMatrixEquation (M : Matrix (Fin 3) (Fin 3) ℂ)
    (i : Fin 2) (z : Fin 2 → ℂ) : ℂ :=
  M i.castSucc 0 * z 0 + M i.castSucc 1 * z 1 + M i.castSucc 2 -
    z i * (M 2 0 * z 0 + M 2 1 * z 1 + M 2 2)

theorem projectiveMatrixEquation_analytic (M : Matrix (Fin 3) (Fin 3) ℂ) (i : Fin 2) :
    AnalyticOnNhd ℂ (projectiveMatrixEquation M i) Set.univ := by
  intro z _
  have hp (j : Fin 2) : AnalyticAt ℂ (fun w : Fin 2 → ℂ => w j) z :=
    (ContinuousLinearMap.proj j : (Fin 2 → ℂ) →L[ℂ] ℂ).analyticAt z
  have hr (j : Fin 3) : AnalyticAt ℂ
      (fun w : Fin 2 → ℂ => M j 0 * w 0 + M j 1 * w 1 + M j 2) z :=
    ((analyticAt_const.mul (hp 0)).add (analyticAt_const.mul (hp 1))).add analyticAt_const
  exact (hr i.castSucc).sub ((hp i).mul (hr 2))

theorem projectiveMatrixEquation_global (M : Matrix (Fin 3) (Fin 3) ℂ)
    {U : Set (Fin 2 → ℂ)} (hU : IsOpen U) (hne : U.Nonempty)
    (h : ∀ z ∈ U, ∀ i, projectiveMatrixEquation M i z = 0) :
    ∀ z i, projectiveMatrixEquation M i z = 0 := by
  obtain ⟨z₀, hz₀⟩ := hne
  intro z i
  have hi := (projectiveMatrixEquation_analytic M i).eqOn_of_preconnected_of_eventuallyEq
    (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : Fin 2 → ℂ => (0 : ℂ)) Set.univ)
    isPreconnected_univ (mem_univ z₀) (by
      filter_upwards [hU.mem_nhds hz₀] with w hw
      exact h w hw i)
  exact hi (mem_univ z)

theorem scalar_matrix_of_projective_open (M : Matrix (Fin 3) (Fin 3) ℂ)
    {U : Set (Fin 2 → ℂ)} (hU : IsOpen U) (hne : U.Nonempty)
    (h : ∀ z ∈ U, ∀ i, projectiveMatrixEquation M i z = 0) :
    M = Matrix.scalar (Fin 3) (M 2 2) := by
  have H := projectiveMatrixEquation_global M hU hne h
  have h02 := H ![0, 0] 0
  have h12 := H ![0, 0] 1
  have hp0 := H ![1, 0] 0
  have hm0 := H ![-1, 0] 0
  have hp1 := H ![0, 1] 1
  have hm1 := H ![0, -1] 1
  have h10 := H ![1, 0] 1
  have h01 := H ![0, 1] 0
  norm_num [projectiveMatrixEquation] at h02 h12 hp0 hm0 hp1 hm1 h10 h01
  have h20 : M 2 0 = 0 := by linear_combination h02 - (1 / 2 : ℂ) * hp0 - (1 / 2 : ℂ) * hm0
  have h21 : M 2 1 = 0 := by linear_combination h12 - (1 / 2 : ℂ) * hp1 - (1 / 2 : ℂ) * hm1
  have h00 : M 0 0 = M 2 2 := by linear_combination hp0 + h20 - h02
  have h11 : M 1 1 = M 2 2 := by linear_combination hp1 + h21 - h12
  have h10' : M 1 0 = 0 := by linear_combination h10 - h12
  have h01' : M 0 1 = 0 := by linear_combination h01 - h02
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.scalar_apply, h00, h11, h01', h10', h02, h12, h20, h21]

end

end OAI.RepresentationTheory.Theta.Geometric.AnalyticCountableSelection
