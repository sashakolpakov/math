import OAI.Analysis.PDE.Variational.CellL2
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Set Filter _root_.MeasureTheory
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Variational

theorem tendsto_toL2_of_dominated
    {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {μ : Measure X} (f : ℕ→X→H) (g : X→H)
    (hf : ∀n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (B : X→ℝ) (hB : MemLp B 2 μ)
    (hbound : ∀n, ∀x, ‖f n x‖≤B x) (hboundg : ∀x, ‖g x‖≤B x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n ↦ (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  have hi : Integrable (fun x ↦ (2*B x)^2) μ := by
    have h := (memLp_two_iff_integrable_sq_norm (hB.const_mul 2).aestronglyMeasurable).mp (hB.const_mul 2)
    simpa only [Real.norm_eq_abs, sq_abs] using h
  have hnorm : ∀n, ‖(hf n).toLp (f n)-hg.toLp g‖^2 = ∫x, ‖f n x-g x‖^2 ∂μ := by
    intro n
    rw [← MemLp.toLp_sub, norm_sq_toLp_eq_integral]
    rfl
  have ht : Tendsto (fun n ↦ ∫x, ‖f n x-g x‖^2 ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence
      (F:=fun n x ↦ ‖f n x-g x‖^2) (f:=fun _ ↦ (0:ℝ)) (fun x ↦ (2*B x)^2)
      (fun n ↦ by
        have hm : AEStronglyMeasurable (fun x ↦ ‖f n x-g x‖) μ :=
          ((hf n).aestronglyMeasurable.sub hg.aestronglyMeasurable).norm
        have hh : AEStronglyMeasurable (fun x ↦ ‖f n x-g x‖*‖f n x-g x‖) μ := hm.mul hm
        simpa only [pow_two] using hh) hi
      (fun n ↦ Eventually.of_forall (fun x ↦ by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        have hB0 : 0≤B x := (norm_nonneg _).trans (hboundg x)
        have hb : ‖f n x-g x‖≤2*B x := (norm_sub_le _ _).trans (by linarith [hbound n x,hboundg x])
        exact pow_le_pow_left₀ (norm_nonneg _) hb 2))
      (hlim.mono fun x hx ↦ by
        have ht : Tendsto (fun n ↦ f n x-g x) atTop (𝓝 (0:H)) := by
          simpa only [sub_self] using hx.sub (tendsto_const_nhds (x:=g x))
        simpa only [sub_self,norm_zero,zero_pow (by decide : (2:ℕ)≠0)] using
          ht.norm.pow 2)
    simpa only [integral_zero] using h
  have ht' : Tendsto (fun n ↦ ‖(hf n).toLp (f n)-hg.toLp g‖^2) atTop (𝓝 0) := by
    simpa only [hnorm] using ht
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs := (Real.continuous_sqrt.tendsto 0).comp ht'
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hs

end OAI.Analysis.PDE.Variational
