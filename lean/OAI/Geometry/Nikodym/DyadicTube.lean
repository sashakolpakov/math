import OAI.Geometry.Nikodym.DyadicCoordinates

open OAI.Analysis.Fourier.Wave

open Set Metric
open scoped Topology

noncomputable section
namespace OAI.Geometry.Nikodym

/-- A uniform finite decomposition of every tube in a fixed coordinate
sector.  The same N works for every direction, center, and tube in the
sector.  Positive and negative line pieces are exact dilates of [1,2]. -/
theorem exists_sector_tube_decomposition_at_scale {d : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (δ : ℝ) :
    ∃ N : ℕ, dyadicRadius N < ρ ∧
      ∀ (ω a x : Space (d+1)) (c : ℝ), ‖ω‖ = 1 → 0 < c → c ≤ |ω 0| →
        x ∈ OAI.MeasureTheory.Kakeya.unitSegment ω a →
        ‖directionSlope ω‖ ≤ c⁻¹ ∧
        ∀ y ∈ OAI.MeasureTheory.Kakeya.tube δ ω a,
          y ∈ ball x (δ+2*ρ/c) ∨
            ∃ j < N, ρ ≤ dyadicRadius j ∧
              (y ∈ neighborhood δ (scaledLinePiece x (directionSlope ω) (dyadicRadius j)) ∨
                y ∈ neighborhood δ (scaledLinePiece x (directionSlope ω) (-dyadicRadius j))) := by
  obtain ⟨N, hN, hdecomp⟩ := exists_finite_dyadic_decomposition hρ
  refine ⟨N, hN, ?_⟩
  intro ω a x c hω hc hcω hx
  refine ⟨directionSlope_norm_le hω hc hcω, ?_⟩
  intro y hy
  obtain ⟨t, ht, hyt⟩ := mem_tube_recenter hx hy
  have hω0abs : 0 < |ω 0| := hc.trans_le hcω
  have hω0 : ω 0 ≠ 0 := abs_pos.mp hω0abs
  have hcoord : |ω 0| ≤ 1 := by
    simpa only [Real.norm_eq_abs, hω] using PiLp.norm_apply_le ω 0
  let s : ℝ := t*ω 0
  have hs : |s| ≤ 1 := by
    dsimp [s]
    rw [abs_mul]
    calc
      |t| * |ω 0| ≤ 1*1 := mul_le_mul (abs_le.mpr ht) hcoord (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hline : x+projectiveJoin d (s • directionSlope ω,s) = x+t • ω := by
    rw [projectiveJoin_directionSlope hω0]
  rcases hdecomp s hs with hsmall | ⟨j,hjN,hjδ,hband⟩
  · left
    have htc : |t| * c ≤ 2*ρ := by
      calc
        |t| * c ≤ |t| * |ω 0| := mul_le_mul_of_nonneg_left hcω (abs_nonneg _)
        _ = |s| := (abs_mul _ _).symm
        _ ≤ 2*ρ := hsmall
    have htnorm : |t| ≤ 2*ρ/c := (le_div_iff₀ hc).mpr htc
    have hdist : dist (x+t • ω) x = |t| := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hω, mul_one, Real.norm_eq_abs]
    rw [mem_ball]
    calc
      dist y x ≤ dist y (x+t • ω) + dist (x+t • ω) x := dist_triangle _ _ _
      _ < δ + |t| := by rw [hdist]; linarith
      _ ≤ δ + 2*ρ/c := by linarith
  · right
    refine ⟨j,hjN,hjδ,?_⟩
    rcases hband with hpos | hneg
    · left
      refine ⟨x+projectiveJoin d (s • directionSlope ω,s), ?_, ?_⟩
      · exact mem_scaledLinePiece_pos x _ (dyadicRadius_pos j) hpos
      · simpa only [hline] using hyt
    · right
      refine ⟨x+projectiveJoin d (s • directionSlope ω,s), ?_, ?_⟩
      · exact mem_scaledLinePiece_neg x _ (dyadicRadius_pos j) hneg
      · simpa only [hline] using hyt

theorem exists_sector_tube_decomposition {d : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, dyadicRadius N < δ ∧
      ∀ (ω a x : Space (d+1)) (c : ℝ), ‖ω‖ = 1 → 0 < c → c ≤ |ω 0| →
        x ∈ OAI.MeasureTheory.Kakeya.unitSegment ω a →
        ‖directionSlope ω‖ ≤ c⁻¹ ∧
        ∀ y ∈ OAI.MeasureTheory.Kakeya.tube δ ω a,
          y ∈ ball x ((2/c+1)*δ) ∨
            ∃ j < N, δ ≤ dyadicRadius j ∧
              (y ∈ neighborhood δ (scaledLinePiece x (directionSlope ω) (dyadicRadius j)) ∨
                y ∈ neighborhood δ (scaledLinePiece x (directionSlope ω) (-dyadicRadius j))) := by
  have he (c : ℝ) : δ+2*δ/c = (2/c+1)*δ := by ring
  simpa only [he] using (exists_sector_tube_decomposition_at_scale (d := d) hδ δ)

/-- Pulling a strip-neighborhood back by its exact signed dilation
costs only δ/|r|, since the coordinate inverse has norm at most one. -/
theorem normalize_scaledLinePiece_neighborhood {d : ℕ} {δ r : ℝ}
    (hr : r ≠ 0) (x : Space (d+1)) (v : Space d) {y : Space (d+1)}
    (hy : y ∈ neighborhood δ (scaledLinePiece x v r)) :
    r⁻¹ • (projectiveJoin d).symm (y-x) ∈ neighborhood (δ/|r|) (linePiece 0 v 1 2) := by
  obtain ⟨z, ⟨p,hp,rfl⟩, hyz⟩ := hy
  refine ⟨p,hp,?_⟩
  have hpull : r⁻¹ • (projectiveJoin d).symm (y-x) - p =
      r⁻¹ • (projectiveJoin d).symm (y-(x+r • projectiveJoin d p)) := by
    rw [show y-(x+r • projectiveJoin d p) = (y-x)-r • projectiveJoin d p by abel]
    simp only [map_sub, map_smul, ContinuousLinearEquiv.symm_apply_apply, smul_sub, smul_smul,
      inv_mul_cancel₀ hr, one_smul]
  rw [dist_eq_norm, hpull, norm_smul, Real.norm_eq_abs, abs_inv]
  calc
    |r|⁻¹ * ‖(projectiveJoin d).symm (y-(x+r • projectiveJoin d p))‖ ≤
        |r|⁻¹ * ‖y-(x+r • projectiveJoin d p)‖ :=
      mul_le_mul_of_nonneg_left (projectiveJoin_symm_norm_le d _) (inv_nonneg.mpr (abs_nonneg _))
    _ < |r|⁻¹ * δ := mul_lt_mul_of_pos_left hyz (inv_pos.mpr (abs_pos.mpr hr))
    _ = δ/|r| := by ring

end OAI.Geometry.Nikodym
