import OAI.Analysis.Fourier.SquareFunction.Square.ExtensionDifference

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory FourierTransform Set
open scoped ENNReal
namespace OAI.Analysis.Fourier.SquareFunction

theorem steinSquareReal_memLp {n : ℕ} {α : ℝ} {p : ℝ≥0∞}
    (f : SchwartzMap (Space n) ℂ)
    (h : MemLp (OAI.Analysis.Fourier.SquareFunction.steinSquareFunction α f) p volume) :
    MemLp (steinSquareReal α f) p volume :=
  (eLpNorm_steinSquareReal_le α f p).trans_lt h

/-- The radius norm is Lipschitz on Schwartz functions in the spatial Lp norm. -/
theorem steinSquareReal_toLp_dist {n : ℕ} [NeZero n] {α : ℝ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hα : 1 / 2 < α) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (OAI.Analysis.Fourier.SquareFunction.steinSquareFunction α f) p volume ≤
        ENNReal.ofReal C * eLpNorm f p volume)
    (f g : SchwartzMap (Space n) ℂ)
    (hf : MemLp (steinSquareReal α f) p volume)
    (hg : MemLp (steinSquareReal α g) p volume) :
    dist (hf.toLp _) (hg.toLp _) ≤ C * dist (f.toLp p volume) (g.toLp p volume) := by
  have h := (eLpNorm_steinSquareReal_sub_le hα f g p).trans (hb (f-g))
  have hfin : ENNReal.ofReal C * eLpNorm (f-g) p volume ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((f-g).memLp p volume).ne
  have ht := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hC] at ht
  rw [dist_eq_norm,← hf.toLp_sub hg,Lp.norm_toLp]
  have hsub : (f-g).toLp p volume = f.toLp p volume - g.toLp p volume :=
    map_sub (SchwartzMap.toLpCLM ℝ ℂ p volume) f g
  rw [dist_eq_norm,← hsub,SchwartzMap.norm_toLp]
  exact ht

end OAI.Analysis.Fourier.SquareFunction
