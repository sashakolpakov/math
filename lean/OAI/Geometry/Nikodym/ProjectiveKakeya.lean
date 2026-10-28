import OAI.Geometry.Nikodym.ProjectiveTube
import OAI.MeasureTheory.Kakeya.Geometry

open OAI.Analysis.Fourier.Wave

noncomputable section
open Set Metric
namespace OAI.Geometry.Nikodym


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem normalized_interval_subset_unitSegment {n : ℕ} (c w : Space n)
    (hw : w ≠ 0) (hwn : ‖w‖ ≤ 2) :
    {y | ∃ t ∈ Icc (1/2 : ℝ) 1, y = c+t • w} ⊆
      OAI.MeasureTheory.Kakeya.unitSegment (‖w‖⁻¹ • w) (c+(3/4 : ℝ) • w) := by
  rintro y ⟨t,ht,rfl⟩
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  refine ⟨(t-3/4)*‖w‖,?_,?_⟩
  · constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr ht.1) hn.le,
      mul_nonneg (sub_nonneg.mpr ht.2) hn.le]
  · rw [smul_smul,mul_assoc,mul_inv_cancel₀ hn.ne',mul_one,
      add_assoc,← add_smul]
    congr 1
    congr 1
    ring

theorem norm_normalized {n : ℕ} {w : Space n} (hw : w ≠ 0) :
    ‖‖w‖⁻¹ • w‖ = 1 := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]

theorem neighborhood_unitSegment_eq_tube {n : ℕ} (δ : ℝ) (ω c : Space n) :
    neighborhood δ (OAI.MeasureTheory.Kakeya.unitSegment ω c) = OAI.MeasureTheory.Kakeya.tube δ ω c := by
  ext y
  constructor
  · rintro ⟨z,⟨t,ht,rfl⟩,hz⟩
    exact OAI.MeasureTheory.Kakeya.mem_tube_iff.mpr ⟨t,ht,hz⟩
  · rintro hy
    obtain ⟨t,ht,hz⟩ := OAI.MeasureTheory.Kakeya.mem_tube_iff.mp hy
    exact ⟨c+t • ω,⟨t,ht,rfl⟩,hz⟩

theorem linear_image_neighborhood {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {δ A : ℝ} (hA : 0 < A) (hL : ‖L‖ ≤ A) (s : Set E) :
    L '' neighborhood δ s ⊆ neighborhood (A*δ) (L '' s) := by
  rintro y ⟨x,⟨z,hz,hd⟩,rfl⟩
  refine ⟨L z,⟨z,hz,rfl⟩,?_⟩
  calc
    dist (L x) (L z) ≤ ‖L‖ * dist x z := L.lipschitzWith.dist_le_mul _ _
    _ ≤ A * dist x z := mul_le_mul_of_nonneg_right hL dist_nonneg
    _ < A * δ := mul_lt_mul_of_pos_left hd hA

/-- A projective line segment in the normalized positive strip fits into
one unit segment with direction determined only by its passing point. -/
theorem linear_transformedLinePiece_subset {n : ℕ}
    (L : (E × ℝ) →L[ℝ] Space n) (x v : E)
    (hw : L (x,1) ≠ 0) (hwn : ‖L (x,1)‖ ≤ 2) :
    L '' transformedLinePiece x v 1 2 ⊆
      OAI.MeasureTheory.Kakeya.unitSegment (‖L (x,1)‖⁻¹ • L (x,1))
        (L (v,0)+(3/4 : ℝ) • L (x,1)) := by
  rintro y ⟨q,⟨s,hs,rfl⟩,rfl⟩
  apply normalized_interval_subset_unitSegment (L (v,0)) (L (x,1)) hw hwn
  refine ⟨s,?_,?_⟩
  · norm_num at hs ⊢
    exact hs
  · simp only [map_add,map_smul]

theorem linear_projective_neighborhood_subset_tube {n : ℕ}
    (L : (E × ℝ) →L[ℝ] Space n) (x v : E) {A X V δ : ℝ}
    (hA : 0 < A) (hL : ‖L‖ ≤ A) (hX : 0 ≤ X) (hV : 0 ≤ V)
    (hx : ‖x‖ ≤ X) (hv : ‖v‖ ≤ V)
    (hw : L (x,1) ≠ 0) (hwn : ‖L (x,1)‖ ≤ 2)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1/2) :
    L '' (projective '' neighborhood δ (linePiece x v 1 2)) ⊆
      OAI.MeasureTheory.Kakeya.tube (A*((2+4*(X+2*V+1))*δ)) (‖L (x,1)‖⁻¹ • L (x,1))
        (L (v,0)+(3/4 : ℝ) • L (x,1)) := by
  have hp := projective_neighborhood_linePiece (x:=x) (v:=v) (a:=1) (b:=2)
    (by norm_num) hX hV hx hv hδ hδhalf
  have hp' : projective '' neighborhood δ (linePiece x v 1 2) ⊆
      neighborhood ((2+4*(X+2*V+1))*δ) (transformedLinePiece x v 1 2) := by
    convert hp using 1 ; ring_nf
  have hi := linear_image_neighborhood L hA hL (transformedLinePiece x v 1 2)
    (δ:=((2+4*(X+2*V+1))*δ))
  rw [← neighborhood_unitSegment_eq_tube]
  intro q hq
  obtain ⟨z,hz,hd⟩ := hi (image_mono hp' hq)
  exact ⟨z,linear_transformedLinePiece_subset L x v hw hwn hz,hd⟩

end OAI.Geometry.Nikodym
