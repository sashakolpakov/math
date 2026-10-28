import OAI.Analysis.PDE.Green.Localized.FiberCutoff
import OAI.Analysis.PDE.Green.Physical.FullProjection

/-! Uniform weighted cutoff control for a time-local extension of the actual
rational fiber defining function. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet
open scoped Topology

theorem normalCutoffWeight_eq_of_sublevel {r R : ℝ}
    (heq : r < 0 → R = r) (hneg : R < 0 ↔ r < 0) (k : ℕ) :
    normalCutoffWeight R k = normalCutoffWeight r k := by
  by_cases h : r < 0
  · rw [heq h]
  · rw [normalCutoffWeight_zero (le_of_not_gt h),
      normalCutoffWeight_zero (le_of_not_gt (fun hR => h (hneg.mp hR)))]

theorem physical_extension_cutoff_weight {d : ℕ}
    (a : ℝ) (R : (ℂ × (Option (Fin d) → ℂ)) → ℝ) {T : Set ℂ}
    (heq : ∀ τ ∈ T, ∀ q, OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0 →
      R =ᶠ[𝓝 (τ, q)] (fun p => OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a p.1 p.2))
    (hneg : ∀ τ ∈ T, ∀ q, R (τ, q) < 0 ↔ OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0)
    {z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3} (hz : energyComplexTime z ∈ T)
    (y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) (k : ℕ) :
    normalCutoffWeight (R (fullPhysicalProjection d (fiberEmbedding (d + 1) 3 z y))) k =
      normalCutoffWeight (OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a (energyComplexTime z)
        (physicalSpatialProjection d y)) k := by
  rw [fullPhysicalProjection_fiber]
  exact normalCutoffWeight_eq_of_sublevel
    (fun h => (heq _ hz _ h.le).eq_of_nhds) (hneg _ hz _) k

/-- The uniform constant depends only on the spatial dimension and coordinate
ordering, not on the time window, scale, extension, or test. -/
theorem exists_uniform_physical_weighted_cutoff_bound {d m : ℕ}
    (c : (Fin (d + 1) × Fin 3) ≃ Fin (m + 1)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (a : ℝ), 0 < a →
      ∀ (T : Set ℂ), (∀ τ ∈ T, a ≤ ‖τ‖ ∧ ‖τ‖ ≤ 4) →
      ∀ (R : (ℂ × (Option (Fin d) → ℂ)) → ℝ), Continuous R →
      (∀ τ ∈ T, ∀ q, OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0 →
        R =ᶠ[𝓝 (τ, q)] (fun p => OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a p.1 p.2)) →
      (∀ τ ∈ T, ∀ q, R (τ, q) < 0 ↔ OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0) →
      ∀ (S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)), MeasurableSet S → Bornology.IsBounded S →
      (∀ z, (fiberEmbedding (d + 1) 3 z) ⁻¹' S ⊆
        euclideanCoordinates c ⁻¹' Icc (physicalBoxLower (physicalOptionCoordinates c))
          (physicalBoxUpper (physicalOptionCoordinates c))) →
      ∀ (η : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → ℝ), Continuous η → Integrable η →
      (energyComplexTime '' tsupport η ⊆ T) → ∀ k : ℕ,
      (∫ x in S, normalCutoffWeight (R (fullPhysicalProjection d x)) k *
        ‖η (timeProjection (d + 1) 3 x)‖) ≤ M * ∫ z, ‖η z‖ := by
  obtain ⟨M, hM, hbound⟩ := exists_uniform_physical_spatial_cutoff_bound c
  refine ⟨M, hM, ?_⟩
  intro a ha T hT R hR heq hneg S hS hSb hsubset η hη hηi hsupport k
  apply weighted_normalCutoff_bound_of_active_fibers hS hSb
    (hR.comp (fullPhysicalProjection d).continuous) hη hηi _ k
  intro z hz j
  have hzT : energyComplexTime z ∈ T :=
    hsupport (mem_image_of_mem energyComplexTime (subset_tsupport _ hz))
  let V := euclideanCoordinates c ⁻¹' Icc (physicalBoxLower (physicalOptionCoordinates c))
    (physicalBoxUpper (physicalOptionCoordinates c))
  have hw : Continuous (fun y => normalCutoffWeight
      (R (fullPhysicalProjection d (fiberEmbedding (d + 1) 3 z y))) j) :=
    (continuous_normalCutoffWeight j).comp
      (hR.comp ((fullPhysicalProjection d).continuous.comp
        ((continuous_fiberEmbedding (d + 1) 3).comp
          (continuous_const.prodMk continuous_id))))
  have hi : IntegrableOn (fun y => normalCutoffWeight
      (R (fullPhysicalProjection d (fiberEmbedding (d + 1) 3 z y))) j) V :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded (isBounded_euclidean_cell c _ _) hw
  calc
    _ ≤ ∫ y in V, normalCutoffWeight
        (R (fullPhysicalProjection d (fiberEmbedding (d + 1) 3 z y))) j := by
      apply setIntegral_mono_set hi
      · exact Filter.Eventually.of_forall (fun y => normalCutoffWeight_nonneg _ _)
      · exact Filter.Eventually.of_forall (hsubset z)
    _ = ∫ y in V, normalCutoffWeight (OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a
        (energyComplexTime z) (physicalSpatialProjection d y)) j := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun y => physical_extension_cutoff_weight a R heq hneg hzT y j)
    _ ≤ M := hbound a _ ha (hT _ hzT).1 (hT _ hzT).2 j

end OAI.Analysis.PDE.Green
