import OAI.Geometry.Nikodym.Majorant
import OAI.Geometry.Nikodym.PieceLp

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped ENNReal
namespace OAI.Geometry.Nikodym


theorem tubeMajorant_lp_bound (hK : OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture)
    {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∀ f : Space (d+1) → ℂ, Measurable f → MemLp f (d+1 : ℕ) volume →
      eLpNorm (tubeMajorant δ N f) (d+1 : ℕ) volume ≤
        ENNReal.ofReal (C*δ^(-ε))*eLpNorm f (d+1 : ℕ) volume := by
  have hV : 0 ≤ slopeBound d := by unfold slopeBound; positivity
  obtain ⟨A,C,hA,hC,h⟩ := exists_piece_lp_bound hK hd hV hε (nearFactor d)
  refine ⟨((d+1:ℕ):ℝ)*(A+4*C),by positivity,?_⟩
  intro N δ hδ hδ1 f hf hfp
  have hp : (1:ℝ≥0∞) ≤ (d+1 : ℕ) := by exact_mod_cast Nat.le_add_left 1 d
  have he : tubeMajorant δ N f =
      ∑ i : Fin (d+1), ∑ k : Option (Fin N × Bool),
        pieceBound δ (stripDilation (slopeBound d)*δ) (nearFactor d) (slopeBound d)
          (coordinateSwap i) f k := by ext x; simp [tubeMajorant]
  rw [he]
  apply (eLpNorm_sum_le hp).trans
  calc
    _ ≤ ∑ _i : Fin (d+1), ENNReal.ofReal ((A+4*C)*δ^(-ε))*eLpNorm f (d+1 : ℕ) volume := by
      apply Finset.sum_le_sum
      intro i _
      exact piece_sum_lp_bound hδ hA.le hC.le (coordinateSwap i) f
        (h N δ hδ hδ1 (coordinateSwap i) f hf hfp)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ ((d+1:ℕ):ℝ)*(A+4*C)),
        ENNReal.ofReal_mul (by positivity : 0 ≤ ((d+1:ℕ):ℝ)),ENNReal.ofReal_natCast,
        ENNReal.ofReal_mul (by positivity : 0 ≤ A+4*C)]
      ac_rfl

end OAI.Geometry.Nikodym
