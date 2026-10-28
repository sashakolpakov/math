import Mathlib

open Set Metric
noncomputable section
namespace OAI.Analysis.PDE.Schauder

/-- A finite refinement of arbitrary positive pointwise ball radii. The
refined radius at each point is fixed before any analytic constants are chosen. -/
theorem compact_refined_ball_cover {X : Type*} [MetricSpace X] [CompactSpace X]
    (r : X → ℝ) (hr : ∀ x, 0 < r x) :
    ∃ s : X → ℝ, (∀ x, 0 < s x) ∧ ∃ t : Finset X,
      ∀ x, ∃ c ∈ t, ∀ y, dist y x ≤ s x → dist y c ≤ r c := by
  classical
  obtain ⟨t, ht⟩ := (isCompact_univ : IsCompact (univ : Set X)).elim_finite_subcover
    (fun x => ball x (r x / 2)) (fun _ => isOpen_ball) (by
      intro x _
      exact mem_iUnion.mpr ⟨x, mem_ball_self (half_pos (hr x))⟩)
  have hcover : ∀ x : X, ∃ c, c ∈ t ∧ dist x c < r c / 2 := by
    intro x
    obtain ⟨c, hc⟩ := mem_iUnion.mp (ht (mem_univ x))
    obtain ⟨hct, hxc⟩ := mem_iUnion.mp hc
    exact ⟨c, hct, mem_ball.mp hxc⟩
  choose c hc hxc using hcover
  refine ⟨fun x => r (c x) / 2, fun x => half_pos (hr (c x)), t, ?_⟩
  intro x
  refine ⟨c x, hc x, ?_⟩
  intro y hy
  exact (dist_triangle y x (c x)).trans (by linarith [hxc x])

/-- The four local quantities in a second-order Schauder estimate.
No derivative identity is encoded here: the periodic application below uses
the actual value, Fréchet derivative, and second Fréchet derivative. -/
def JetBoundOnBall {X F₀ F₁ F₂ : Type*} [MetricSpace X]
    [NormedAddCommGroup F₀] [NormedAddCommGroup F₁] [NormedAddCommGroup F₂]
    (f₀ : X → F₀) (f₁ : X → F₁) (f₂ : X → F₂) (α : ℝ) (x : X) (r M : ℝ) : Prop :=
  ∀ y, dist y x ≤ r → ‖f₀ y‖ ≤ M ∧ ‖f₁ y‖ ≤ M ∧ ‖f₂ y‖ ≤ M ∧
    ∀ z, dist z x ≤ r → ‖f₂ y-f₂ z‖ ≤ M * dist y z ^ α

/-- Pointwise-center constants become one uniform constant after passing to
a fixed finite refinement. The local radius is chosen before the small error. -/
theorem compact_pointwise_jet_constants
    {X F₀ F₁ F₂ I : Type*} [MetricSpace X] [CompactSpace X]
    [NormedAddCommGroup F₀] [NormedAddCommGroup F₁] [NormedAddCommGroup F₂]
    (f₀ : I → X → F₀) (f₁ : I → X → F₁) (f₂ : I → X → F₂)
    (α : ℝ) (H N : I → ℝ) (hN : ∀ i, 0 ≤ N i)
    (hlocal : ∀ x : X, ∃ r > 0, ∀ ε > 0, ∃ D > 0, ∀ i,
      JetBoundOnBall (f₀ i) (f₁ i) (f₂ i) α x r (ε * H i + D * N i)) :
    ∃ r : X → ℝ, (∀ x, 0 < r x) ∧ ∀ ε > 0, ∃ D > 0, ∀ i x,
      JetBoundOnBall (f₀ i) (f₁ i) (f₂ i) α x (r x) (ε * H i + D * N i) := by
  classical
  choose r hr hloc using hlocal
  obtain ⟨s, hs, t, ht⟩ := compact_refined_ball_cover r hr
  refine ⟨s, hs, ?_⟩
  intro ε hε
  choose D hD hbound using (fun x => hloc x ε hε)
  let B := 1 + ∑ x ∈ t, D x
  have hsum : 0 ≤ ∑ x ∈ t, D x := Finset.sum_nonneg (fun x _ => (hD x).le)
  have hB : 0 < B := by dsimp only [B]; linarith
  refine ⟨B, hB, ?_⟩
  intro i x
  obtain ⟨c, hct, hc⟩ := ht x
  have hcB : D c ≤ B := by
    have hd := Finset.single_le_sum (fun z (_ : z ∈ t) => (hD z).le) hct
    dsimp only [B]
    linarith
  have hbudget : ε * H i + D c * N i ≤ ε * H i + B * N i :=
    add_le_add le_rfl (mul_le_mul_of_nonneg_right hcB (hN i))
  intro y hy
  obtain ⟨h₀, h₁, h₂, hh⟩ := hbound c i y (hc y hy)
  refine ⟨h₀.trans hbudget, h₁.trans hbudget, h₂.trans hbudget, ?_⟩
  intro z hz
  exact (hh z (hc z hz)).trans
    (mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg dist_nonneg _))

end OAI.Analysis.PDE.Schauder
