import OAI.Analysis.Fourier.Dispersion.Massive

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Dispersion

def MassiveLocalSmoothing : Prop :=
  ∀ n : ℕ, 2≤n → ∀ m p ε : ℝ, 2≤p → (0<ε ∨ (p=2 ∧ ε=0)) →
    ∃ C : ℝ, 0<C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (OAI.Analysis.Fourier.LocalSmoothing.besselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p+ε) f) (ENNReal.ofReal p) ∧
      MemLp (fun z : Space n × ℝ ↦ massiveHalfWave m z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ∧
      eLpNorm (fun z : Space n × ℝ ↦ massiveHalfWave m z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal C * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.besselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p+ε) f)
        (ENNReal.ofReal p) volume

def MassiveLogarithmicSobolev : Prop :=
  ∀ n : ℕ, 2≤n → ∀ m p B : ℝ, 2<p → 2*n+6<B →
    ∃ C : ℝ, 0<C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p) B f) (ENNReal.ofReal p) ∧
      MemLp (fun z : Space n × ℝ ↦ massiveHalfWave m z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ∧
      eLpNorm (fun z : Space n × ℝ ↦ massiveHalfWave m z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal C * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential (OAI.Analysis.Fourier.LocalSmoothing.smoothingOrder n p) B f)
        (ENNReal.ofReal p) volume

theorem massiveLocalSmoothing_of_localSmoothing (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing) :
    MassiveLocalSmoothing := by
  intro n hn m p ε hp hε
  obtain ⟨C,hC,hb⟩ := massive_localSmoothing hls hn m hp hε
  refine ⟨C,hC,fun f ↦ ⟨OAI.Analysis.Fourier.BesselPotential.memLp_besselPotential _ f _,?_,hb f⟩⟩
  exact lt_of_le_of_lt (hb f) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (OAI.Analysis.Fourier.BesselPotential.memLp_besselPotential _ f _).eLpNorm_lt_top)

theorem massiveLogarithmicSobolev_of_logarithmicSobolev (hlog : OAI.Analysis.Fourier.LocalSmoothing.LogarithmicSobolev) :
    MassiveLogarithmicSobolev := by
  intro n hn m p B hp hB
  obtain ⟨C,hC,hb⟩ := massive_logarithmicSobolev hlog hn m hp hB
  refine ⟨C,hC,fun f ↦ ⟨OAI.Analysis.Fourier.BesselPotential.memLp_logBesselPotential _ _ f _,?_,hb f⟩⟩
  exact lt_of_le_of_lt (hb f) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (OAI.Analysis.Fourier.BesselPotential.memLp_logBesselPotential _ _ f _).eLpNorm_lt_top)

end OAI.Analysis.Fourier.Dispersion
