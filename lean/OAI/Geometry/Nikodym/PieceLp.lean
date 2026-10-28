import OAI.Geometry.Nikodym.PieceCover

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped ENNReal
namespace OAI.Geometry.Nikodym


theorem sum_dyadicRadius_le (N : ℕ) : (∑ j : Fin N, dyadicRadius j) ≤ 2 := by
  have he : (∑ j : Fin N, dyadicRadius j) = 2*(1-dyadicRadius N) := by
    induction N with
    | zero => simp [dyadicRadius]
    | succ N ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc,Fin.val_last]
      rw [ih]
      unfold dyadicRadius
      rw [pow_succ]
      ring
  rw [he]
  have := (dyadicRadius_pos N).le
  linarith

def pieceWeight {N : ℕ} (A C : ℝ) : Option (Fin N × Bool) → ℝ
  | none => A
  | some (j,_) => C*dyadicRadius j

theorem pieceWeight_nonneg {N : ℕ} {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (k : Option (Fin N × Bool)) : 0 ≤ pieceWeight A C k := by
  cases k with
  | none => exact hA
  | some k => exact mul_nonneg hC (dyadicRadius_pos k.1).le

theorem sum_pieceWeight_le (N : ℕ) {A C : ℝ} (hC : 0 ≤ C) :
    (∑ k : Option (Fin N × Bool), pieceWeight A C k) ≤ A+4*C := by
  simp only [Fintype.sum_option,Fintype.sum_prod_type,Fintype.sum_bool,pieceWeight]
  have h := mul_le_mul_of_nonneg_left (sum_dyadicRadius_le N) hC
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  linarith

theorem exists_piece_lp_bound (hK : OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture)
    {d : ℕ} (hd : 1 ≤ d) {V ε : ℝ} (hV : 0 ≤ V) (hε : 0 < ε) (K : ℝ) :
    ∃ A C : ℝ, 0 < A ∧ 0 < C ∧ ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ L : Space (d+1) ≃ₗᵢ[ℝ] Space (d+1), ∀ f : Space (d+1) → ℂ,
      Measurable f → MemLp f (d+1 : ℕ) volume → ∀ k : Option (Fin N × Bool),
      eLpNorm (pieceBound δ (stripDilation V*δ) K V L f k) (d+1 : ℕ) volume ≤
        ENNReal.ofReal (pieceWeight A C k*δ^(-ε)) * eLpNorm f (d+1 : ℕ) volume := by
  obtain ⟨A,hA,hball⟩ := exists_ballAverage_lp_bound d K
  obtain ⟨C,hC,hstrip⟩ := rotatedStrip_lp_bound hK hd hV hε
  refine ⟨A,C,hA,hC,?_⟩
  intro N δ hδ hδ1 L f hf hfp k
  cases k with
  | none =>
    apply (hball δ hδ f hf).trans
    apply mul_le_mul' (ENNReal.ofReal_le_ofReal _) le_rfl
    apply mul_le_mul_of_nonneg_left _ hA.le
    exact hδ1.trans (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (neg_nonpos.mpr hε.le))
  | some k =>
    rcases k with ⟨j,b⟩
    by_cases hcut : stripDilation V*δ ≤ dyadicRadius j
    · have h := hstrip (signedDyadicRadius j b) δ (signedDyadicRadius_ne_zero j b)
        (by rw [abs_signedDyadicRadius]; exact dyadicRadius_le_one j) hδ
        (by simpa only [abs_signedDyadicRadius] using hcut) L f hf hfp
      simpa only [pieceBound,ite_eq_left hcut,pieceWeight,abs_signedDyadicRadius,mul_right_comm] using h
    · simp [pieceBound,hcut]

theorem piece_sum_lp_bound {d N : ℕ} {δ V ε K A C : ℝ}
    (hδ : 0 < δ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (L : Space (d+1) ≃ₗᵢ[ℝ] Space (d+1)) (f : Space (d+1) → ℂ)
    (h : ∀ k : Option (Fin N × Bool),
      eLpNorm (pieceBound δ (stripDilation V*δ) K V L f k) (d+1 : ℕ) volume ≤
        ENNReal.ofReal (pieceWeight A C k*δ^(-ε))*eLpNorm f (d+1 : ℕ) volume) :
    eLpNorm (∑ k : Option (Fin N × Bool), pieceBound δ (stripDilation V*δ) K V L f k)
      (d+1 : ℕ) volume ≤ ENNReal.ofReal ((A+4*C)*δ^(-ε))*eLpNorm f (d+1 : ℕ) volume := by
  have hp : (1:ℝ≥0∞) ≤ (d+1 : ℕ) := by exact_mod_cast Nat.le_add_left 1 d
  apply (eLpNorm_sum_le hp).trans
  apply (Finset.sum_le_sum (fun k _ => h k)).trans
  rw [← Finset.sum_mul,← ENNReal.ofReal_sum_of_nonneg]
  · apply mul_le_mul' (ENNReal.ofReal_le_ofReal _) le_rfl
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_pieceWeight_le N hC) (Real.rpow_pos_of_pos hδ _).le
  · intro k _
    exact mul_nonneg (pieceWeight_nonneg hA hC k) (Real.rpow_pos_of_pos hδ _).le

end OAI.Geometry.Nikodym
