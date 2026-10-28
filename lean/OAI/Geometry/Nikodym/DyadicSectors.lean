import OAI.Geometry.Nikodym.DyadicTube

open OAI.Analysis.Fourier.Wave

open Set Metric
open scoped Topology BigOperators

noncomputable section
namespace OAI.Geometry.Nikodym

/-- The finite coordinate changes used to place a direction in the
zeroth-coordinate projective chart.  Each is an exact linear isometry. -/
def coordinateSwap {d : ℕ} (i : Fin (d+1)) : Space (d+1) ≃ₗᵢ[ℝ] Space (d+1) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 0 i)

@[simp] theorem coordinateSwap_zero {d : ℕ} (i : Fin (d+1)) (ω : Space (d+1)) :
    coordinateSwap i ω 0 = ω i := by
  simp [coordinateSwap, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

theorem exists_large_coordinate {d : ℕ} {ω : Space (d+1)} (hω : ‖ω‖ = 1) :
    ∃ i : Fin (d+1), ((d:ℝ)+2)⁻¹ ≤ |ω i| := by
  by_contra! h
  have hd : 0 < (d:ℝ)+2 := by positivity
  have hterm (i : Fin (d+1)) : (ω i)^2 ≤ ((d:ℝ)+2)⁻¹ := by
    have hi : |ω i| ≤ 1 := by
      simpa only [Real.norm_eq_abs, hω] using PiLp.norm_apply_le ω i
    have habs := abs_nonneg (ω i)
    have hsquare : (ω i)^2 = |ω i|^2 := (sq_abs _).symm
    nlinarith [h i]
  have hsum : (∑ i : Fin (d+1), (ω i)^2) = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, hω]
    norm_num
  have hbound : 1 ≤ ((d:ℝ)+1) * ((d:ℝ)+2)⁻¹ := by
    have H := Finset.sum_le_sum (s := Finset.univ) (fun i hi => hterm i)
    simpa only [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using H
  have hstrict : ((d:ℝ)+1) * ((d:ℝ)+2)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hd]
    linarith
  exact (not_lt_of_ge hbound) hstrict

theorem exists_coordinate_sector {d : ℕ} {ω : Space (d+1)} (hω : ‖ω‖ = 1) :
    ∃ i : Fin (d+1), ((d:ℝ)+2)⁻¹ ≤ |coordinateSwap i ω 0| := by
  simpa only [coordinateSwap_zero] using exists_large_coordinate hω

theorem linearIsometry_mem_tube_iff {n : ℕ} (e : Space n ≃ₗᵢ[ℝ] Space n)
    (δ : ℝ) (ω a y : Space n) :
    e y ∈ OAI.MeasureTheory.Kakeya.tube δ (e ω) (e a) ↔ y ∈ OAI.MeasureTheory.Kakeya.tube δ ω a := by
  simp only [OAI.MeasureTheory.Kakeya.mem_tube_iff]
  have he (t : ℝ) : e (a+t • ω) = e a+t • e ω := by simp
  simp only [← he, e.dist_map]

theorem linearIsometry_mem_segment_iff {n : ℕ} (e : Space n ≃ₗᵢ[ℝ] Space n)
    (ω a x : Space n) :
    e x ∈ OAI.MeasureTheory.Kakeya.unitSegment (e ω) (e a) ↔ x ∈ OAI.MeasureTheory.Kakeya.unitSegment ω a := by
  change (∃ t ∈ Icc (-(1/2:ℝ)) (1/2), e x=e a+t • e ω) ↔
    (∃ t ∈ Icc (-(1/2:ℝ)) (1/2), x=a+t • ω)
  have he (t : ℝ) : e (a+t • ω) = e a+t • e ω := by simp
  simp only [← he, e.injective.eq_iff]

theorem coordinateSwap_tube {d : ℕ} (i : Fin (d+1)) (δ : ℝ) (ω a : Space (d+1)) :
    coordinateSwap i '' OAI.MeasureTheory.Kakeya.tube δ ω a =
      OAI.MeasureTheory.Kakeya.tube δ (coordinateSwap i ω) (coordinateSwap i a) := by
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact (linearIsometry_mem_tube_iff _ _ _ _ _).mpr hz
  · intro hy
    refine ⟨(coordinateSwap i).symm y, ?_, by simp⟩
    apply (linearIsometry_mem_tube_iff (coordinateSwap i) δ ω a _).mp
    simpa using hy

end OAI.Geometry.Nikodym
