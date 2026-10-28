import OAI.RepresentationTheory.Theta.Adelic.QuadraticNormOperations

/-! # Quadratic Square Ball -/

namespace OAI.RepresentationTheory.Theta.Adelic.QuadraticSquareBall

noncomputable section

/-! Exact small-ball images of squaring in the general norm-one chart and
the principal unit chart. The common radius controls the parameter d. -/

open scoped _root_.Topology

open Set _root_.Metric Filter
open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormOperations

theorem normSquareCoordinate_norm
    {k : Type*} [NormedField k] [IsUltrametricDist k] (d x : k)
    (r : ℝ) (hr1 : r ≤ 1) (hdr : ‖d‖ * r ≤ 1) (hx : ‖x‖ < r) :
    ‖QuadraticNormOperations.normSquareCoordinate d x‖ = ‖(2 : k)‖ * ‖x‖ := by
  have hn : ‖1 + d * x ^ 2‖ = 1 := by
    simpa only [pow_two, mul_assoc] using QuadraticNormOperations.one_add_mul_norm_eq_one d x x r hr1 hdr hx hx
  rw [QuadraticNormOperations.normSquareCoordinate, norm_div, norm_mul, hn, div_one]

theorem normSquareCoordinate_map_nhds
    {k : Type*} [NontriviallyNormedField k] [CompleteSpace k] [CharZero k] (d : k) :
    Filter.map (QuadraticNormOperations.normSquareCoordinate d) (𝓝 (0 : k)) = 𝓝 (0 : k) := by
  have hd : HasStrictDerivAt (QuadraticNormOperations.normSquareCoordinate d) 2 0 := by
    simpa [QuadraticNormOperations.normSquareCoordinate] using!
      (((hasStrictDerivAt_id (0 : k)).const_mul 2).div
        ((hasStrictDerivAt_const (0 : k) (1 : k)).add
          (((hasStrictDerivAt_id (0 : k)).pow 2).const_mul d)) (by norm_num))
  simpa [QuadraticNormOperations.normSquareCoordinate] using hd.map_nhds_eq (by norm_num : (2 : k) ≠ 0)

theorem exists_common_square_ball_radius
    {k : Type*} [NontriviallyNormedField k] [CompleteSpace k] [CharZero k] [IsUltrametricDist k]
    (d : k) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ r ≤ ‖(2 : k)‖ ∧ ‖d‖ * r ≤ 1 ∧
      (Weil.Local.SquareBall.Construction.principalSquareCoordinate : k → k) '' Metric.ball 0 r = Metric.ball 0 (‖(2 : k)‖ * r) ∧
      (QuadraticNormOperations.normSquareCoordinate d) '' Metric.ball 0 r = Metric.ball 0 (‖(2 : k)‖ * r) := by
  have h2 : 0 < ‖(2 : k)‖ := norm_pos_iff.mpr (by norm_num)
  let R : ℝ := (‖d‖ + 1)⁻¹
  have hd0 : 0 < ‖d‖ + 1 := by positivity
  have hR : 0 < R := inv_pos.mpr hd0
  have hR1 : R ≤ 1 := by
    apply (inv_le_one₀ hd0).mpr
    linarith [norm_nonneg d]
  have hdR : ‖d‖ * R ≤ 1 := by
    change ‖d‖ * (‖d‖ + 1)⁻¹ ≤ 1
    rw [← div_eq_mul_inv, div_le_one hd0]
    linarith
  obtain ⟨r₁, hr₁, hr₁b, h₁⟩ := Weil.Local.BallImage.Construction.small_ball_image_of_norm_identity
    (Weil.Local.SquareBall.Construction.principalSquareCoordinate : k → k) ‖(2 : k)‖ ‖(2 : k)‖ h2 h2
    Weil.Local.SquareBall.Construction.principalSquareCoordinate_map_nhds Weil.Local.SquareBall.Construction.principalSquareCoordinate_norm
  obtain ⟨r₂, hr₂, hr₂b, h₂⟩ := Weil.Local.BallImage.Construction.small_ball_image_of_norm_identity
    (QuadraticNormOperations.normSquareCoordinate d) ‖(2 : k)‖ R h2 hR (normSquareCoordinate_map_nhds d)
    (fun x hx => normSquareCoordinate_norm d x R hR1 hdR hx)
  let r := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  have hrr₁ : r ≤ r₁ := min_le_left _ _
  have hrr₂ : r ≤ r₂ := min_le_right _ _
  exact ⟨r, hr, (hrr₂.trans hr₂b).trans hR1, hrr₁.trans hr₁b,
    (mul_le_mul_of_nonneg_left (hrr₂.trans hr₂b) (norm_nonneg d)).trans hdR,
    h₁ r hr hrr₁, h₂ r hr hrr₂⟩

end

end OAI.RepresentationTheory.Theta.Adelic.QuadraticSquareBall
