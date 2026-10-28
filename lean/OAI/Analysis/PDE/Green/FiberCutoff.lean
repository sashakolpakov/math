import OAI.Analysis.PDE.Green.CellFiber
import OAI.Analysis.PDE.Green.NormalCutoff

/-! Fiberwise normal-cutoff control yields the correct L1 time-test bound. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set _root_.MeasureTheory OAI.Analysis.PDE.Dirichlet

theorem weighted_normalCutoff_bound_of_fibers {n s : ℕ}
    {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s)} (hS : MeasurableSet S) (hb : Bornology.IsBounded S)
    {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ} (hr : Continuous r)
    {η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s → ℝ} (hηc : Continuous η) (hηi : Integrable η)
    {M : ℝ}
    (hM : ∀ z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s, ∀ k : ℕ,
      (∫ y in (fiberEmbedding n s z) ⁻¹' S,
        normalCutoffWeight (r (fiberEmbedding n s z y)) k) ≤ M)
    (k : ℕ) :
    (∫ x in S, normalCutoffWeight (r x) k * ‖η (timeProjection n s x)‖) ≤
      M * ∫ z, ‖η z‖ := by
  have hw : Continuous (fun x => normalCutoffWeight (r x) k) :=
    (continuous_normalCutoffWeight k).comp hr
  have hi : IntegrableOn (fun x => ‖η (timeProjection n s x)‖ * normalCutoffWeight (r x) k) S :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb
      ((hηc.comp (timeProjection n s).continuous).norm.mul hw)
  have he := integral_set_time_weight hS (fun z => ‖η z‖) hi
  have hreorder : (∫ x in S, normalCutoffWeight (r x) k * ‖η (timeProjection n s x)‖) =
      ∫ x in S, ‖η (timeProjection n s x)‖ * normalCutoffWeight (r x) k := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => mul_comm _ _)
  rw [hreorder, he, ← integral_const_mul]
  refine integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun z => mul_nonneg (norm_nonneg _)
      (integral_nonneg (fun y => normalCutoffWeight_nonneg _ _)))) (hηi.norm.const_mul M) ?_
  apply Filter.Eventually.of_forall
  intro z
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hM z k) (norm_nonneg (η z))

end OAI.Analysis.PDE.Green
