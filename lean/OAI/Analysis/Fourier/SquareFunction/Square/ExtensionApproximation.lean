import OAI.Analysis.Fourier.SquareFunction.Square.ExtensionLocalSmoothing

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Set Filter
open scoped ENNReal Topology
namespace OAI.Analysis.Fourier.SquareFunction.SquareLpExtension

variable {n : ℕ} {α : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Schwartz approximations genuinely exist for every Lp class. -/
theorem exists_schwartz_approximation (hp : p ≠ ⊤)
    (f : Lp ℂ p (volume : Measure (Space n))) :
    ∃ g : ℕ → SchwartzMap (Space n) ℂ,
      Tendsto (fun i => (g i).toLp p volume) atTop (𝓝 f) := by
  classical
  have hd := SchwartzMap.denseRange_toLpCLM (E := Space n) (F := ℂ) (μ := volume) hp
  obtain ⟨s,hs,ht⟩ := mem_closure_iff_seq_limit.mp (hd f)
  choose g hg using hs
  refine ⟨g,?_⟩
  have he : (fun i => (g i).toLp p volume) = s := funext hg
  rw [he]
  exact ht

/-- The radius square function of each Schwartz datum lies in Lp whenever
the full-Lp extension exists. This uses its actual a.e. agreement. -/
theorem memLp_real (S : SquareLpExtension n α p) (f : SchwartzMap (Space n) ℂ) :
    MemLp (steinSquareReal α f) p volume :=
  (Lp.memLp (S.toFun (f.toLp p volume))).ae_eq (S.schwartz f)

theorem toLp_eq (S : SquareLpExtension n α p) (f : SchwartzMap (Space n) ℂ)
    (hf : MemLp (steinSquareReal α f) p volume) :
    hf.toLp _ = S.toFun (f.toLp p volume) :=
  Lp.ext (hf.coeFn_toLp.trans (S.schwartz f).symm)

/-- The actual square functions, converted to Lp classes, converge for
every Schwartz approximation, and the limit is independent of that choice. -/
theorem tendsto_squareFunctions (S : SquareLpExtension n α p)
    {ι : Type*} {l : Filter ι} (f : Lp ℂ p (volume : Measure (Space n)))
    (g : ι → SchwartzMap (Space n) ℂ)
    (hg : Tendsto (fun i => (g i).toLp p volume) l (𝓝 f)) :
    Tendsto (fun i => (S.memLp_real (g i)).toLp _) l (𝓝 (S.toFun f)) := by
  simpa only [S.toLp_eq] using S.tendsto_of_schwartz_approximation f g hg

theorem approximation_limit_unique (S : SquareLpExtension n α p)
    {ι : Type*} {l : Filter ι} [NeBot l]
    (f : Lp ℂ p (volume : Measure (Space n)))
    (g : ι → SchwartzMap (Space n) ℂ)
    (hg : Tendsto (fun i => (g i).toLp p volume) l (𝓝 f))
    {v : Lp ℝ p (volume : Measure (Space n))}
    (hv : Tendsto (fun i => (S.memLp_real (g i)).toLp _) l (𝓝 v)) :
    v = S.toFun f := tendsto_nhds_unique hv (S.tendsto_squareFunctions f g hg)

end OAI.Analysis.Fourier.SquareFunction.SquareLpExtension
