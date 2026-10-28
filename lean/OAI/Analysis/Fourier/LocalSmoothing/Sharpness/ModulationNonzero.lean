import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.ModulationData
import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.AnnularPacket
import Mathlib.MeasureTheory.Function.LpSpace.Complete

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory Filter Set
open scoped Topology ENNReal
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

theorem eLpNorm_eq_zero_of_norm_tendsto {X I : Type*} [MeasurableSpace X]
    {μ : Measure X} {u : Filter I} [NeBot u] [IsCountablyGenerated u]
    {F : I → X → ℂ} {g : X → ℂ} {p : ℝ≥0∞}
    (hF : ∀ i, AEStronglyMeasurable (F i) μ) (hg : AEStronglyMeasurable g μ)
    (hpoint : ∀ x, Tendsto (fun i => F i x) u (𝓝 (g x)))
    (hnorm : Tendsto (fun i => eLpNorm (F i) p μ) u (𝓝 0)) :
    eLpNorm g p μ = 0 := by
  apply le_antisymm ?_ bot_le
  apply le_of_forall_gt
  intro B hB
  obtain ⟨b,hb,hbB⟩ := exists_between hB
  exact (Lp.eLpNorm_le_of_ae_tendsto
    ((hnorm.eventually (gt_mem_nhds hb)).mono fun i hi => hi.le) hF hg
    (Eventually.of_forall hpoint)).trans_lt hbB

theorem traveling_bump_eLpNorm_ne_zero {n : ℕ} (ω : Space n)
    (f : SchwartzMap (Space n) ℂ) (hf : f ≠ 0) {p : ℝ≥0∞} (hp : p ≠ 0) :
    eLpNorm (fun z : Space n × ℝ => f (z.1-z.2•ω)) p (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≠ 0 := by
  intro hz
  have hae := (eLpNorm_eq_zero_iff hp).mp hz
  have hm : MeasurableSet {z : Space n × ℝ | f (z.1-z.2•ω)=0} :=
    (isClosed_eq (by fun_prop) continuous_const).measurableSet
  have htime : ∀ᵐ t ∂(volume.restrict (Icc (1:ℝ) 2)),
      ∀ᵐ x ∂volume, f (x-t•ω)=0 :=
    (Measure.ae_ae_comm hm).mp ((Measure.ae_prod_iff_ae_ae hm).mp hae)
  have hmeasure : (volume.restrict (Icc (1:ℝ) 2)) univ = 1 := by
    norm_num [Real.volume_Icc]
  have : NeZero (volume.restrict (Icc (1:ℝ) 2)) := ⟨by
    intro h
    simp [h] at hmeasure⟩
  obtain ⟨t,ht⟩ := htime.exists
  have he : (fun x : Space n => f (x-t•ω)) = (0 : Space n → ℂ) :=
    (Continuous.ae_eq_iff_eq volume (by fun_prop) continuous_const).mp ht
  apply hf
  ext x
  have h := congrFun he (x+t•ω)
  simpa using h

theorem exists_nonzero_bandlimited_bump {n : ℕ} (hn : 0 < n) :
    ∃ ω : Space n, ‖ω‖=1 ∧ ∃ f : SchwartzMap (Space n) ℂ,
      f ≠ 0 ∧ ∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → ‖ξ‖ ≤ 2 := by
  let ω : Space n := EuclideanSpace.single ⟨0,hn⟩ 1
  have hω : ‖ω‖=1 := by simp [ω]
  obtain ⟨f,hf,hF⟩ := OAI.Analysis.Fourier.Restriction.exists_schwartz_angularInverse_pair
    (OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialSymbol_contDiff n) (OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialSymbol_hasCompactSupport n)
  have hcenter : OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialSymbol n ((3/2:ℝ)•ω) = 1 := by
    have hnorm : ‖(3/2:ℝ)•ω‖=3/2 := by rw [norm_smul,hω]; norm_num
    have hb : OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialBump (3/2) = 1 :=
      OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialBump.one_of_mem_closedBall (by
        simp only [Metric.mem_closedBall,dist_self,OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialBump]
        norm_num)
    simp only [OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialSymbol,hnorm,hb,Complex.ofReal_one]
  refine ⟨ω,hω,f,?_,?_⟩
  · intro hz
    have hh := hF ((3/2:ℝ)•ω)
    rw [hcenter,hz] at hh
    simp [OAI.Analysis.Fourier.LocalSmoothing.angularFourier] at hh
  · intro ξ hξ
    rw [hF] at hξ
    exact (OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialSymbol_support n (subset_tsupport _ hξ)).2

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
