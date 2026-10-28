import OAI.Analysis.Fourier.SquareFunction.Square.ExtensionDense
import OAI.Analysis.Fourier.SquareFunction.Square.ExtensionNorm

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Filter
open scoped ENNReal Topology
namespace OAI.Analysis.Fourier.SquareFunction

/-- The full-Lp realization of Stein's nonnegative square function. Its
Schwartz agreement is almost everywhere, as appropriate for an Lp operator. -/
structure SquareLpExtension (n : ℕ) (α : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] where
  toFun : Lp ℂ p (volume : Measure (Space n)) → Lp ℝ p (volume : Measure (Space n))
  constant : NNReal
  constant_pos : 0 < constant
  lipschitz : LipschitzWith constant toFun
  zero : toFun 0 = 0
  schwartz : ∀ f : SchwartzMap (Space n) ℂ,
    ⇑(toFun (f.toLp p volume)) =ᵐ[volume] steinSquareReal α f

theorem exists_squareLpExtension_of_bound {n : ℕ} [NeZero n] {α : ℝ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hα : 1 / 2 < α)
    {C : ℝ} (hC : 0 < C)
    (hb : ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (OAI.Analysis.Fourier.SquareFunction.steinSquareFunction α f) p volume ≤
        ENNReal.ofReal C * eLpNorm f p volume) :
    Nonempty (SquareLpExtension n α p) := by
  have hm (f : SchwartzMap (Space n) ℂ) : MemLp (steinSquareReal α f) p volume := by
    apply (eLpNorm_steinSquareReal_le α f p).trans_lt
    exact (hb f).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (f.memLp p volume))
  let s : SchwartzMap (Space n) ℂ → Lp ℝ p (volume : Measure (Space n)) :=
    fun f => (hm f).toLp _
  obtain ⟨T,hT,hTi,hunique⟩ := exists_lipschitz_extension_dense
    (SchwartzMap.toLpCLM ℝ ℂ p volume) (SchwartzMap.denseRange_toLpCLM hp)
    s ⟨C,hC.le⟩ (fun f g => steinSquareReal_toLp_dist hα hC.le hb f g (hm f) (hm g))
  have hs0 : s 0 = 0 := by
    apply norm_eq_zero.mp
    rw [show ‖s 0‖ = (eLpNorm (steinSquareReal α 0) p volume).toReal from Lp.norm_toLp _ _]
    have h : eLpNorm (steinSquareReal α (0 : SchwartzMap (Space n) ℂ)) p volume = 0 := by
      apply le_antisymm _ zero_le
      simpa using (eLpNorm_steinSquareReal_le α (0 : SchwartzMap (Space n) ℂ) p).trans (hb 0)
    rw [h,ENNReal.toReal_zero]
  refine ⟨⟨T,⟨C,hC.le⟩,hC,hT,?_,?_⟩⟩
  · simpa only [map_zero,hs0] using hTi 0
  · intro f
    rw [show T (f.toLp p volume) = s f from hTi f]
    exact (hm f).coeFn_toLp

namespace SquareLpExtension

variable {n : ℕ} {α : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem continuous (S : SquareLpExtension n α p) : Continuous S.toFun :=
  S.lipschitz.continuous

theorem norm_le (S : SquareLpExtension n α p) (f : Lp ℂ p (volume : Measure (Space n))) :
    ‖S.toFun f‖ ≤ S.constant * ‖f‖ := by
  simpa only [S.zero,dist_zero_right] using S.lipschitz.dist_le_mul f 0

theorem schwartz_enorm [NeZero n] (S : SquareLpExtension n α p) (hα : 1 / 2 < α)
    (f : SchwartzMap (Space n) ℂ) :
    (fun x => ‖S.toFun (f.toLp p volume) x‖ₑ) =ᵐ[volume]
      OAI.Analysis.Fourier.SquareFunction.steinSquareFunction α f :=
  (S.schwartz f).fun_comp (fun x => ‖x‖ₑ) |>.trans (ae_enorm_steinSquareReal hα f)

/-- The extension is uniquely determined by continuity and its actual
Schwartz values, not by a choice of approximating sequence. -/
theorem unique (S : SquareLpExtension n α p) (hp : p ≠ ⊤)
    (T : Lp ℂ p (volume : Measure (Space n)) → Lp ℝ p (volume : Measure (Space n)))
    (hT : Continuous T)
    (hTs : ∀ f : SchwartzMap (Space n) ℂ,
      ⇑(T (f.toLp p volume)) =ᵐ[volume] steinSquareReal α f) : T = S.toFun := by
  have hd := SchwartzMap.denseRange_toLpCLM (E := Space n) (F := ℂ) (μ := volume) hp
  funext f
  exact hd.induction_on f (isClosed_eq hT S.continuous)
    (fun g => Lp.ext ((hTs g).trans (S.schwartz g).symm))

/-- Every Schwartz approximation converges to the same square-function
value in the full spatial Lp norm. -/
theorem tendsto_of_schwartz_approximation (S : SquareLpExtension n α p)
    {ι : Type*} {l : Filter ι} (f : Lp ℂ p (volume : Measure (Space n)))
    (g : ι → SchwartzMap (Space n) ℂ)
    (hg : Tendsto (fun i => (g i).toLp p volume) l (𝓝 f)) :
    Tendsto (fun i => S.toFun ((g i).toLp p volume)) l (𝓝 (S.toFun f)) :=
  S.continuous.continuousAt.tendsto.comp hg

end SquareLpExtension
end OAI.Analysis.Fourier.SquareFunction
