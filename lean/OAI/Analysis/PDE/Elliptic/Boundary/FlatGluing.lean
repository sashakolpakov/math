import OAI.Analysis.PDE.Elliptic.Boundary.ProjectionGluing
import OAI.Analysis.PDE.Elliptic.Boundary.SlopeFromGradient

/-! Full closed-half-ball Hölder control from boundary traces, normal
approach, and relative interior estimates. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Metric InnerProductSpace

theorem exists_flat_boundary_holder_constant
    {E Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [NormedAddCommGroup Y] {ν : E} (hν : ‖ν‖ = 1)
    {a b c κ A B C V : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hb1 : b < 1) (hc : 0 < c) (hκ : 0 < κ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hV : 0 ≤ V) :
    ∃ γ D : ℝ, 0 < γ ∧ γ < 1 ∧ 0 < D ∧ ∀ f : E → Y,
      (∀ x ∈ closedHalfBall ν, ‖f x‖ ≤ V) →
      (∀ z, ‖z‖ ≤ 1 / 8 → inner ℝ ν z = 0 → ∀ h : ℝ,
        0 < h → h ≤ 1 / 8 → ‖f (z + h • ν) - f z‖ ≤ A * h ^ a) →
      (∀ z z', ‖z‖ ≤ 1 / 8 → ‖z'‖ ≤ 1 / 8 →
        inner ℝ ν z = 0 → inner ℝ ν z' = 0 →
        ‖f z - f z'‖ ≤ C * ‖z - z'‖ ^ c) →
      (∀ x, ‖x‖ ≤ 1 / 4 → 0 < inner ℝ ν x →
        ∀ y ∈ closedBall x (κ * inner ℝ ν x / 2),
        ‖f y - f x‖ ≤ B * (‖y - x‖ / inner ℝ ν x) ^ b) →
      ∀ x y, ‖x‖ ≤ 1 / 8 → ‖y‖ ≤ 1 / 8 → 0 ≤ inner ℝ ν x →
        0 ≤ inner ℝ ν y → ‖f x - f y‖ ≤ D * ‖x - y‖ ^ γ := by
  let K := {x : E | ‖x‖ ≤ 1 / 8 ∧ 0 ≤ inner ℝ ν x}
  let height := fun x : E => inner ℝ ν x
  let proj := fun x : E => x - height x • ν
  have hheight (x : E) : |height x| ≤ ‖x‖ := by
    simpa [height, hν] using abs_real_inner_le_norm ν x
  have hproj (x : E) : ‖proj x‖ ≤ ‖x‖ := norm_tangential_part_le ν x hν
  have hproj0 (x : E) : inner ℝ ν (proj x) = 0 := by
    simp [proj, height, inner_sub_right, real_inner_smul_right, hν]
  have hhlip (x y : E) : height y ≤ height x + dist x y := by
    have ht := abs_real_inner_le_norm ν (y - x)
    rw [hν, one_mul, inner_sub_right] at ht
    rw [dist_eq_norm, norm_sub_rev x y]
    dsimp [height]
    linarith [(abs_le.mp ht).2]
  have hplip (x y : E) : ‖proj x - proj y‖ ≤ ‖x - y‖ := by
    have he : proj x - proj y = (x - y) - (inner ℝ ν (x - y)) • ν := by
      simp only [proj, height, inner_sub_right, sub_smul]
      abel
    rw [he]
    exact norm_tangential_part_le ν (x - y) hν
  obtain ⟨γ, D, hγ, hγ1, hD, hglue⟩ :=
    exists_holder_constant_of_boundary_projection (Y := Y) (K := K)
      (height := height) (proj := proj) ha hb hb1 hc hκ hA hB hC hV
      (fun x hx => ⟨hx.2, (le_abs_self _).trans ((hheight x).trans (by linarith [hx.1]))⟩)
      (fun x _ y _ => hhlip x y)
      (fun x hx y hy => by
        rw [dist_eq_norm]
        exact (norm_sub_le x y).trans (by linarith [hx.1, hy.1]))
  refine ⟨γ, D, hγ, hγ1, hD, ?_⟩
  intro f hbound happ htrace hint
  have hresult := hglue f
    (fun x hx => hbound x ⟨by linarith [hx.1], hx.2⟩)
    (fun x hx => ?_)
    (fun x hx y hy => ?_)
    (fun x hx y hy hh hxy => ?_)
  · intro x y hx hy hxν hyν
    simpa only [dist_eq_norm] using hresult x ⟨hx, hxν⟩ y ⟨hy, hyν⟩
  · by_cases hh : height x = 0
    · have he : proj x = x := by simp [proj, hh]
      rw [he, sub_self, norm_zero]
      positivity
    · have hhpos : 0 < height x := lt_of_le_of_ne hx.2 (Ne.symm hh)
      have hh8 : height x ≤ 1 / 8 := (le_abs_self _).trans ((hheight x).trans hx.1)
      have he : proj x + height x • ν = x := sub_add_cancel _ _
      have ht := happ (proj x) ((hproj x).trans hx.1) (hproj0 x) (height x) hhpos hh8
      rwa [he] at ht
  · have ht := htrace (proj x) (proj y) ((hproj x).trans hx.1)
      ((hproj y).trans hy.1) (hproj0 x) (hproj0 y)
    exact ht.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) ((hplip x y).trans_eq (dist_eq_norm x y).symm) hc.le) hC)
  · rw [norm_sub_rev (f x) (f y)]
    have hyball : y ∈ closedBall x (κ * inner ℝ ν x / 2) := by
      rw [mem_closedBall, dist_comm y x]
      exact hxy
    have ht := hint x (by linarith [hx.1]) hh y hyball
    simpa only [norm_sub_rev y x, dist_eq_norm] using ht

end OAI.Analysis.PDE.Elliptic
