import OAI.Geometry.Nikodym.DyadicGeometry
import OAI.Geometry.Nikodym.Coordinates
import OAI.MeasureTheory.Kakeya.Geometry

open OAI.Analysis.Fourier.Wave

open Set Metric
open scoped Topology

noncomputable section
namespace OAI.Geometry.Nikodym

def directionSlope {d : ℕ} (ω : Space (d+1)) : Space d :=
  (ω 0)⁻¹ • ((projectiveJoin d).symm ω).1

theorem directionSlope_norm_le {d : ℕ} {ω : Space (d+1)} {c : ℝ}
    (hω : ‖ω‖ = 1) (hc : 0 < c) (hcω : c ≤ |ω 0|) :
    ‖directionSlope ω‖ ≤ c⁻¹ := by
  have hpos : 0 < |ω 0| := hc.trans_le hcω
  have hfirst : ‖((projectiveJoin d).symm ω).1‖ ≤ 1 :=
    (norm_fst_le _).trans ((projectiveJoin_symm_norm_le d ω).trans_eq hω)
  rw [directionSlope, norm_smul, Real.norm_eq_abs, abs_inv]
  calc
    |ω 0|⁻¹ * ‖((projectiveJoin d).symm ω).1‖ ≤ |ω 0|⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left hfirst (inv_nonneg.mpr hpos.le)
    _ ≤ c⁻¹ := by simpa using inv_anti₀ hc hcω

theorem projectiveJoin_directionSlope {d : ℕ} {ω : Space (d+1)}
    (hω0 : ω 0 ≠ 0) (t : ℝ) :
    projectiveJoin d ((t*ω 0) • directionSlope ω, t*ω 0) = t • ω := by
  ext i
  cases i using Fin.cases with
  | zero => simp
  | succ i =>
    simp only [projectiveJoin_succ, directionSlope, PiLp.smul_apply,
      projectiveJoin_symm_first, smul_eq_mul]
    field_simp [hω0]

/-- Recenter a tube at any point of its central unit segment. -/
theorem mem_tube_recenter {d : ℕ} {δ : ℝ} {ω a x y : Space d}
    (hx : x ∈ OAI.MeasureTheory.Kakeya.unitSegment ω a) (hy : y ∈ OAI.MeasureTheory.Kakeya.tube δ ω a) :
    ∃ t ∈ Icc (-1 : ℝ) 1, dist y (x+t • ω) < δ := by
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, hyt⟩ := OAI.MeasureTheory.Kakeya.mem_tube_iff.mp hy
  refine ⟨t-s, ⟨by linarith [hs.2,ht.1], by linarith [ht.2,hs.1]⟩, ?_⟩
  convert hyt using 2
  rw [sub_smul]
  abel

def scaledLinePiece {d : ℕ} (x : Space (d+1)) (v : Space d) (r : ℝ) : Set (Space (d+1)) :=
  (fun p => x+r • projectiveJoin d p) '' linePiece 0 v 1 2

theorem mem_scaledLinePiece {d : ℕ} (x : Space (d+1)) (v : Space d)
    {r s : ℝ} (hr : r ≠ 0) (hs : s/r ∈ Icc (1 : ℝ) 2) :
    x + projectiveJoin d (s • v,s) ∈ scaledLinePiece x v r := by
  refine ⟨((s/r) • v,s/r), ⟨s/r,hs,by simp⟩, ?_⟩
  change x+r • projectiveJoin d ((s/r) • v,s/r) = x+projectiveJoin d (s • v,s)
  congr 1
  rw [← map_smul]
  congr 1
  apply Prod.ext
  · change r • ((s/r) • v) = s • v
    rw [smul_smul, mul_div_cancel₀ _ hr]
  · change r*(s/r)=s
    exact mul_div_cancel₀ s hr

theorem mem_scaledLinePiece_pos {d : ℕ} (x : Space (d+1)) (v : Space d)
    {r s : ℝ} (hr : 0 < r) (hs : s ∈ Icc r (2*r)) :
    x + projectiveJoin d (s • v,s) ∈ scaledLinePiece x v r := by
  apply mem_scaledLinePiece x v hr.ne'
  exact ⟨(le_div_iff₀ hr).mpr (by simpa using hs.1), (div_le_iff₀ hr).mpr hs.2⟩

theorem mem_scaledLinePiece_neg {d : ℕ} (x : Space (d+1)) (v : Space d)
    {r s : ℝ} (hr : 0 < r) (hs : -s ∈ Icc r (2*r)) :
    x + projectiveJoin d (s • v,s) ∈ scaledLinePiece x v (-r) := by
  apply mem_scaledLinePiece x v (neg_ne_zero.mpr hr.ne')
  rw [div_neg, ← neg_div]
  exact ⟨(le_div_iff₀ hr).mpr (by simpa using hs.1), (div_le_iff₀ hr).mpr hs.2⟩

end OAI.Geometry.Nikodym
