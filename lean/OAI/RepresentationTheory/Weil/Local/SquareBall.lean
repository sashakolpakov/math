import OAI.RepresentationTheory.Weil.Local.BallImage
import Mathlib.Analysis.Normed.Field.Ultra

/-! # Square Ball -/

namespace OAI.RepresentationTheory.Weil.Local.SquareBall.Construction

noncomputable section

/-! Exact images of sufficiently small nonarchimedean balls under the two local square maps. -/

open Set _root_.Metric Filter
open scoped _root_.Topology

def principalSquareCoordinate {k : Type*} [Field k] (x : k) : k := 2 * x + x ^ 2

def normOneSquareCoordinate {k : Type*} [Field k] (x : k) : k := 2 * x / (1 - x ^ 2)

theorem principalSquareCoordinate_norm
    {k : Type*} [NormedField k] [IsUltrametricDist k] (x : k) (hx : ‖x‖ < ‖(2 : k)‖) :
    ‖principalSquareCoordinate x‖ = ‖(2 : k)‖ * ‖x‖ := by
  have hn : ‖(2 : k) + x‖ = ‖(2 : k)‖ := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hx.ne', max_eq_left hx.le]
  rw [principalSquareCoordinate, show 2 * x + x ^ 2 = ((2 : k) + x) * x by ring,
    norm_mul, hn]

theorem normOneSquareCoordinate_norm
    {k : Type*} [NormedField k] [IsUltrametricDist k] (x : k) (hx : ‖x‖ < 1) :
    ‖normOneSquareCoordinate x‖ = ‖(2 : k)‖ * ‖x‖ := by
  have hx2 : ‖-(x ^ 2)‖ < ‖(1 : k)‖ := by
    rw [norm_neg, norm_pow, norm_one]
    nlinarith [norm_nonneg x]
  have hn : ‖(1 : k) - x ^ 2‖ = 1 := by
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hx2.ne',
      max_eq_left hx2.le, norm_one]
  rw [normOneSquareCoordinate, norm_div, norm_mul, hn, div_one]

theorem principalSquareCoordinate_map_nhds
    {k : Type*} [NontriviallyNormedField k] [CompleteSpace k] [CharZero k] :
    Filter.map (principalSquareCoordinate : k → k) (𝓝 (0 : k)) = 𝓝 (0 : k) := by
  have hd : HasStrictDerivAt (principalSquareCoordinate : k → k) 2 0 := by
    simpa [principalSquareCoordinate] using!
      ((hasStrictDerivAt_id (0 : k)).const_mul 2).add ((hasStrictDerivAt_id (0 : k)).pow 2)
  simpa [principalSquareCoordinate] using hd.map_nhds_eq (by norm_num : (2 : k) ≠ 0)

theorem normOneSquareCoordinate_map_nhds
    {k : Type*} [NontriviallyNormedField k] [CompleteSpace k] [CharZero k] :
    Filter.map (normOneSquareCoordinate : k → k) (𝓝 (0 : k)) = 𝓝 (0 : k) := by
  have hd : HasStrictDerivAt (normOneSquareCoordinate : k → k) 2 0 := by
    simpa [normOneSquareCoordinate] using!
      (((hasStrictDerivAt_id (0 : k)).const_mul 2).div
        ((hasStrictDerivAt_const (0 : k) (1 : k)).sub ((hasStrictDerivAt_id (0 : k)).pow 2))
        (by norm_num))
  simpa [normOneSquareCoordinate] using hd.map_nhds_eq (by norm_num : (2 : k) ≠ 0)

theorem exists_common_square_ball_radius
    {k : Type*} [NontriviallyNormedField k] [CompleteSpace k] [CharZero k] [IsUltrametricDist k] :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ min 1 ‖(2 : k)‖ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      (principalSquareCoordinate : k → k) '' Metric.ball 0 r = Metric.ball 0 (‖(2 : k)‖ * r) ∧
      (normOneSquareCoordinate : k → k) '' Metric.ball 0 r = Metric.ball 0 (‖(2 : k)‖ * r) := by
  have h2 : 0 < ‖(2 : k)‖ := norm_pos_iff.mpr (by norm_num)
  obtain ⟨r₁, hr₁, hr₁b, h₁⟩ := BallImage.Construction.small_ball_image_of_norm_identity
    (principalSquareCoordinate : k → k) ‖(2 : k)‖ ‖(2 : k)‖ h2 h2
    principalSquareCoordinate_map_nhds principalSquareCoordinate_norm
  obtain ⟨r₂, hr₂, hr₂b, h₂⟩ := BallImage.Construction.small_ball_image_of_norm_identity
    (normOneSquareCoordinate : k → k) ‖(2 : k)‖ 1 h2 zero_lt_one
    normOneSquareCoordinate_map_nhds normOneSquareCoordinate_norm
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂,
    le_min ((min_le_right _ _).trans hr₂b) ((min_le_left _ _).trans hr₁b), ?_⟩
  intro r hr hrr
  exact ⟨h₁ r hr (hrr.trans (min_le_left _ _)), h₂ r hr (hrr.trans (min_le_right _ _))⟩

end

end OAI.RepresentationTheory.Weil.Local.SquareBall.Construction
