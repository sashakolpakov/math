import OAI.Geometry.Nikodym.DyadicSectors

open OAI.Analysis.Fourier.Wave

open Set Metric
open scoped Topology

noncomputable section
namespace OAI.Geometry.Nikodym

/-- Finite-coordinate and finite-dyadic decomposition of every actual
Nikodym tube.  The cutoff scale is independent of the tube thickness,
so normalized strips can be made as thin as required. -/
theorem exists_finite_coordinate_tube_decomposition {d : ℕ} {ρ : ℝ}
    (hρ : 0 < ρ) (δ : ℝ) :
    ∃ N : ℕ, dyadicRadius N < ρ ∧
      ∀ (ω a x : Space (d+1)), ‖ω‖ = 1 → x ∈ OAI.MeasureTheory.Kakeya.unitSegment ω a →
        ∃ i : Fin (d+1),
          ‖directionSlope (coordinateSwap i ω)‖ ≤ (d:ℝ)+2 ∧
          ∀ y ∈ OAI.MeasureTheory.Kakeya.tube δ ω a,
            y ∈ ball x (δ+2*ρ*((d:ℝ)+2)) ∨
              ∃ j < N, ρ ≤ dyadicRadius j ∧
                (coordinateSwap i y ∈ neighborhood δ
                  (scaledLinePiece (coordinateSwap i x) (directionSlope (coordinateSwap i ω))
                    (dyadicRadius j)) ∨
                 coordinateSwap i y ∈ neighborhood δ
                  (scaledLinePiece (coordinateSwap i x) (directionSlope (coordinateSwap i ω))
                    (-dyadicRadius j))) := by
  obtain ⟨N,hN,hdecomp⟩ := exists_sector_tube_decomposition_at_scale (d := d) hρ δ
  refine ⟨N,hN,?_⟩
  intro ω a x hω hx
  obtain ⟨i,hi⟩ := exists_coordinate_sector hω
  have hd : 0 < (d:ℝ)+2 := by positivity
  have hsω : ‖coordinateSwap i ω‖ = 1 := by simpa using hω
  have hsx : coordinateSwap i x ∈ OAI.MeasureTheory.Kakeya.unitSegment (coordinateSwap i ω) (coordinateSwap i a) :=
    (linearIsometry_mem_segment_iff _ _ _ _).mpr hx
  obtain ⟨hv,hy⟩ := hdecomp (coordinateSwap i ω) (coordinateSwap i a) (coordinateSwap i x)
    ((d:ℝ)+2)⁻¹ hsω (inv_pos.mpr hd) hi hsx
  refine ⟨i,by simpa only [inv_inv] using hv,?_⟩
  intro y hyt
  rcases hy (coordinateSwap i y) ((linearIsometry_mem_tube_iff _ _ _ _ _).mpr hyt) with hnear | hfar
  · left
    simpa only [mem_ball, LinearIsometryEquiv.dist_map, div_inv_eq_mul] using hnear
  · exact Or.inr hfar

end OAI.Geometry.Nikodym
