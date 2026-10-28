import OAI.Analysis.PDE.Concentration.Packet.Compact
import OAI.Analysis.PDE.Concentration.PatchVolume

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green

theorem integrableOn_packet_product {d : ℕ} {S : Set (OAI.Analysis.Calculus.Current.SpatialSpace d)}
    {T : Set (Option (Fin d) → ℂ)} (hS : MeasurableSet S) (hT : MeasurableSet T)
    {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3 → ℝ}
    (hf : IntegrableOn f ((physicalPacketSplit d) ⁻¹' (S ×ˢ T))) :
    IntegrableOn (fun p : OAI.Analysis.Calculus.Current.SpatialSpace d × (Option (Fin d) → ℂ) =>
      f (spatialPacketEmbedding d p.1 p.2)) (S ×ˢ T) := by
  let e := physicalPacketSplit d
  have hST := hS.prod hT
  have hpre : MeasurableSet (e ⁻¹' (S ×ˢ T)) := hST.preimage e.measurable
  have hi := (measurePreserving_physicalPacketSplit d).symm.integrable_comp_of_integrable
    ((integrable_indicator_iff hpre).mpr hf)
  have heq : (fun p => ((e ⁻¹' (S ×ˢ T)).indicator f) (e.symm p)) =
      (S ×ˢ T).indicator (fun p => f (spatialPacketEmbedding d p.1 p.2)) := by
    ext p
    have hp : e.symm p ∈ e ⁻¹' (S ×ˢ T) ↔ p ∈ S ×ˢ T := by
      change e (e.symm p) ∈ S ×ˢ T ↔ _
      rw [e.apply_symm_apply]
    by_cases h : p ∈ S ×ˢ T
    · rw [Set.indicator_of_mem (hp.mpr h), Set.indicator_of_mem h]
      congr 1
      exact physicalPacketSplit_symm d p.1 p.2
    · rw [Set.indicator_of_notMem (fun hc => h (hp.mp hc)), Set.indicator_of_notMem h]
  change Integrable (fun p => ((e ⁻¹' (S ×ˢ T)).indicator f) (e.symm p)) volume at hi
  rw [heq] at hi
  exact (integrable_indicator_iff hST).mp hi

theorem product_patch_integral_lower {d : ℕ} {S : Set (OAI.Analysis.Calculus.Current.SpatialSpace d)}
    {T P : Set (Option (Fin d) → ℂ)} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hP : MeasurableSet P) (hPT : P ⊆ T) (hPf : volume P ≠ ⊤)
    {f : OAI.Analysis.Calculus.Current.SpatialSpace d × (Option (Fin d) → ℂ) → ℝ} {g : OAI.Analysis.Calculus.Current.SpatialSpace d → ℝ}
    (hf : IntegrableOn f (S ×ˢ T)) (hg : IntegrableOn g S)
    (hf0 : ∀ p ∈ S ×ˢ T, 0 ≤ f p) (c : ℝ)
    (hlower : ∀ y ∈ S, ∀ q ∈ P, c * g y ≤ f (y, q)) :
    c * volume.real P * (∫ y in S, g y) ≤ ∫ p in S ×ˢ T, f p := by
  have hpconst : Integrable (fun _ : Option (Fin d) → ℂ => (1 : ℝ)) (volume.restrict P) :=
    integrableOn_const hPf
  have hgprod : IntegrableOn (fun p : OAI.Analysis.Calculus.Current.SpatialSpace d × (Option (Fin d) → ℂ) => c * g p.1)
      (S ×ˢ P) := by
    have hh := (hg.const_mul c).mul_prod hpconst
    change Integrable _ (volume.restrict (S ×ˢ P))
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    simpa only [mul_one] using hh
  have hsub : S ×ˢ P ⊆ S ×ˢ T := Set.prod_mono subset_rfl hPT
  have hlow := setIntegral_mono_on hgprod (hf.mono_set hsub) (hS.prod hP)
    (fun p hp => hlower p.1 hp.1 p.2 hp.2)
  have hmono := setIntegral_mono_set hf ((ae_restrict_iff' (hS.prod hT)).mpr
    (Filter.Eventually.of_forall hf0)) (Filter.Eventually.of_forall hsub)
  have he : (∫ p in S ×ˢ P, c * g p.1) = c * volume.real P * (∫ y in S, g y) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    calc
      _ = (∫ y in S, c * g y) * (∫ _ in P, (1 : ℝ)) := by
        simpa only [mul_one] using integral_prod_mul (fun y => c * g y)
          (fun _ : Option (Fin d) → ℂ => (1 : ℝ))
      _ = _ := by
        rw [integral_const_mul, integral_const]
        simp only [smul_eq_mul, mul_one, measureReal_restrict_apply_univ]
        ring
  rw [he] at hlow
  exact hlow.trans hmono

/-- Integrate a lower density on any measurable subpatch of the physical
fiber, in the exact rotated Green cell and with its actual volume. -/
theorem physical_patch_integral_lower {d : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (a : ℝ) (τ : ℂ)
    {P : Set (Option (Fin d) → ℂ)}
    (hT : MeasurableSet {q : Option (Fin d) → ℂ | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0})
    (hP : MeasurableSet P) (hPT : P ⊆ {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0})
    (hPf : volume P ≠ ⊤) {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3 → ℝ} {g : OAI.Analysis.Calculus.Current.SpatialSpace d → ℝ}
    (hf : IntegrableOn f (spatialFiberEquiv (sideHundredLattice (spatialFramePi R)) ''
      OAI.Analysis.PDE.Green.physicalSpatialFiber d a τ)) (hg : IntegrableOn g (closedPhysicalSpatialCell R))
    (hf0 : ∀ y, spatialDefiningFunction d a τ y < 0 → 0 ≤ f y) (c : ℝ)
    (hlower : ∀ y ∈ closedPhysicalSpatialCell R, ∀ q ∈ P, c * g y ≤ f (spatialPacketEmbedding d y q)) :
    c * volume.real P * (∫ y in physicalSpatialCell R, g y) ≤
      ∫ y in spatialFiberEquiv (sideHundredLattice (spatialFramePi R)) '' OAI.Analysis.PDE.Green.physicalSpatialFiber d a τ, f y := by
  rw [physicalPacketSplit_latticeCell] at hf ⊢
  have hS := (isCompact_closedPhysicalSpatialCell R).measurableSet
  have hprod := integrableOn_packet_product hS hT hf
  have hl := product_patch_integral_lower hS hT hP hPT hPf hprod hg
    (fun p hp => hf0 _ (by rw [spatialPacketEmbedding_defining]; exact hp.2)) c hlower
  rw [integral_closedPhysicalSpatialCell R] at hl
  apply hl.trans_eq
  rw [physicalPacketSplit_setIntegral hS hT hf]
  rw [Measure.volume_eq_prod] at hprod ⊢
  rw [setIntegral_prod _ hprod]
  exact integral_integral_swap
    (by simpa only [Measure.prod_restrict, IntegrableOn, Function.uncurry_def] using hprod)

theorem isCompact_physicalOutputPatch {d : ℕ} (a : ℝ) (τ : ℂ) (γ : ℝ)
    (_ : 0 < a) (_ : a ≤ ‖τ‖) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1 / 100) :
    IsCompact (physicalOutputPatch (d := d) a τ γ) := by
  apply (isCompact_outputParameterPatch d γ).image_of_continuousOn
  intro u hu
  exact (OAI.Analysis.Calculus.Current.contDiffAt_physicalFiberInverse a τ u (OAI.Analysis.Calculus.Current.fiberParameterBall_denominator
    (OAI.Analysis.PDE.Green.openFiberParameterBall_subset d (outputParameterPatch_subset hγ hγ1 hu)))).continuousAt.continuousWithinAt

end OAI.Analysis.PDE.Concentration
