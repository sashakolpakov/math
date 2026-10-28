import OAI.Analysis.PDE.Green.FiberCutoff
import OAI.Analysis.PDE.Green.Physical.CellGeometry

/-! Only fibers reached by the time test need a cutoff-mass bound. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet

theorem weighted_normalCutoff_bound_of_active_fibers {n s : ℕ}
    {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s)} (hS : MeasurableSet S) (hb : Bornology.IsBounded S)
    {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 1) s → ℝ} (hr : Continuous r)
    {η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s → ℝ} (hηc : Continuous η) (hηi : Integrable η)
    {M : ℝ}
    (hM : ∀ z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 s, η z ≠ 0 → ∀ k : ℕ,
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
  by_cases hz : η z = 0
  · simp only [hz, norm_zero, zero_mul, mul_zero, le_refl]
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hM z hz k) (norm_nonneg (η z))

theorem exists_uniform_physical_spatial_cutoff_bound {d m : ℕ}
    (c : (Fin (d + 1) × Fin 3) ≃ Fin (m + 1)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (a : ℝ) (τ : ℂ), 0 < a → a ≤ ‖τ‖ → ‖τ‖ ≤ 4 →
      ∀ k : ℕ, (∫ y in euclideanCoordinates c ⁻¹'
          Icc (physicalBoxLower (physicalOptionCoordinates c))
            (physicalBoxUpper (physicalOptionCoordinates c)),
        normalCutoffWeight (OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ
          (physicalSpatialProjection d y)) k) ≤ M := by
  obtain ⟨M, hM, hbound⟩ := exists_uniform_physical_cutoff_bound d (physicalOptionCoordinates c)
  refine ⟨M, hM, ?_⟩
  intro a τ ha ht ht' k
  have heq := (measurePreserving_euclideanCoordinates c).setIntegral_preimage_emb
    (euclideanCoordinates c).toHomeomorph.measurableEmbedding
    (fun x => normalCutoffWeight (OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ
      (complexSpatialProjection (physicalOptionCoordinates c) x)) k)
    (Icc (physicalBoxLower (physicalOptionCoordinates c))
      (physicalBoxUpper (physicalOptionCoordinates c)))
  simp only [complexSpatialProjection_euclidean] at heq
  rw [heq]
  exact hbound a τ ha ht ht' k

end OAI.Analysis.PDE.Green
