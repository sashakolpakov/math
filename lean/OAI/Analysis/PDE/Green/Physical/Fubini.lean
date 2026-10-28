import OAI.Analysis.PDE.Green.ProductVolume
import OAI.Analysis.PDE.Green.Physical.Periodic

/-! Identification of the real-coordinate fiber volume with the physical
periodic real / complex spatial volume. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Dirichlet
open scoped ContDiff

def physicalSpatialEquiv (d : ℕ) : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3 ≃ᵐ
    ((Fin (d + 1) → ℝ) × (Option (Fin d) → ℂ)) :=
  (spatialRealComplexEquiv (Fin (d + 1))).trans
    ((MeasurableEquiv.refl _).prodCongr
      (MeasurableEquiv.piCongrLeft (fun _ => ℂ) (finSuccEquiv d)))

theorem measurePreserving_physicalSpatialEquiv (d : ℕ) :
    MeasurePreserving (physicalSpatialEquiv d) :=
  (measurePreserving_spatialRealComplexEquiv (Fin (d + 1))).trans
    ((MeasurePreserving.id volume).prod
      (volume_measurePreserving_piCongrLeft (fun _ => ℂ) (finSuccEquiv d)))

def physicalSpatialEmbedding (d : ℕ) (x : Fin (d + 1) → ℝ) (q : Option (Fin d) → ℂ) :
    OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3 := (physicalSpatialEquiv d).symm (x, q)

theorem physicalSpatialEmbedding_eq (d : ℕ) (x : Fin (d + 1) → ℝ)
    (q : Option (Fin d) → ℂ) :
    physicalSpatialEmbedding d x q =
      spatialRealComplexEmbedding (Fin (d + 1)) x (fun i => q (finSuccEquiv d i)) := rfl

theorem contDiff_physicalSpatialEmbedding (d : ℕ) (k : ℕ∞ω) :
    ContDiff ℝ k (fun p : (Fin (d + 1) → ℝ) × (Option (Fin d) → ℂ) =>
      physicalSpatialEmbedding d p.1 p.2) := by
  simp only [physicalSpatialEmbedding_eq]
  have hq : ContDiff ℝ k
      (fun p : (Fin (d + 1) → ℝ) × (Option (Fin d) → ℂ) =>
        fun i => p.2 (finSuccEquiv d i)) := by fun_prop
  exact (contDiff_spatialRealComplexEmbedding (Fin (d + 1)) k).comp
    (contDiff_fst.prodMk hq)

def physicalSpatialFiber (d : ℕ) (a : ℝ) (τ : ℂ) : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3) :=
  (physicalSpatialEquiv d) ⁻¹'
    (Icc (0 : Fin (d + 1) → ℝ) 1 ×ˢ {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0})

theorem isOpen_physical_fiber {d : ℕ} (a : ℝ) (τ : ℂ) (ha : 0 < a) (ht : a ≤ ‖τ‖) :
    IsOpen {q : Option (Fin d) → ℂ | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0} := by
  apply (OAI.Analysis.Calculus.Current.contDiffOn_physicalFiberDefining (1 / 10) a τ).continuousOn.isOpen_preimage
    (OAI.Analysis.Calculus.Current.isOpen_physicalRegularDomain τ) ?_ isOpen_Iio
  intro q hq
  change OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0 at hq
  exact OAI.Analysis.Calculus.Current.physical_fiber_collar_subset_regular a τ ha ht (by change OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 1; linarith)

theorem physicalSpatialFiber_integral {d : ℕ} (a : ℝ) (τ : ℂ) (ha : 0 < a)
    (ht : a ≤ ‖τ‖) {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3 → ℝ}
    (hf : IntegrableOn f (physicalSpatialFiber d a τ)) :
    (∫ y in physicalSpatialFiber d a τ, f y) =
      ∫ x in Icc (0 : Fin (d + 1) → ℝ) 1,
        ∫ q in {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0},
          f (physicalSpatialEmbedding d x q) := by
  classical
  let e := physicalSpatialEquiv d
  let K := Icc (0 : Fin (d + 1) → ℝ) 1
  let D := {q : Option (Fin d) → ℂ | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0}
  have hKD : MeasurableSet (K ×ˢ D) := measurableSet_Icc.prod
    (isOpen_physical_fiber a τ ha ht).measurableSet
  have hS : MeasurableSet (e ⁻¹' (K ×ˢ D)) := hKD.preimage e.measurable
  have hmp := (measurePreserving_physicalSpatialEquiv d).symm
  have hi := hmp.integrable_comp_of_integrable ((integrable_indicator_iff hS).2 hf)
  have he : (fun p => ((e ⁻¹' (K ×ˢ D)).indicator f) (e.symm p)) =
      (K ×ˢ D).indicator (fun p => f (e.symm p)) := by
    funext p
    have hp : e.symm p ∈ e ⁻¹' (K ×ˢ D) ↔ p ∈ K ×ˢ D := by
      change e (e.symm p) ∈ K ×ˢ D ↔ p ∈ K ×ˢ D
      rw [e.apply_symm_apply]
    simp only [indicator, hp]
  have hp : IntegrableOn (fun p => f (e.symm p)) (K ×ˢ D) :=
    (integrable_indicator_iff hKD).1 (he ▸ hi)
  change (∫ y in e ⁻¹' (K ×ˢ D), f y) = _
  rw [← integral_indicator hS]
  calc
    _ = ∫ p, ((e ⁻¹' (K ×ˢ D)).indicator f) (e.symm p) :=
      (hmp.integral_comp e.symm.measurableEmbedding _).symm
    _ = ∫ p in K ×ˢ D, f (e.symm p) := by rw [he, integral_indicator hKD]
    _ = _ := by
      rw [Measure.volume_eq_prod] at hp ⊢
      exact setIntegral_prod _ hp

theorem physicalSpatialFiber_bounded (d : ℕ) (a : ℝ) (τ : ℂ) (ha : 0 < a)
    (ht : a ≤ ‖τ‖) : Bornology.IsBounded (physicalSpatialFiber d a τ) := by
  have hK := isCompact_Icc (α := Fin (d + 1) → ℝ)
    (a := 0) (b := 1)
  have hD := OAI.Analysis.Calculus.Current.isCompact_physical_fiber_sublevel (d := d) a τ ha ht (0 : ℝ) (by norm_num)
  have hc := (hK.prod hD).image (contDiff_physicalSpatialEmbedding d 0).continuous
  apply hc.isBounded.subset
  intro y hy
  refine ⟨physicalSpatialEquiv d y, ⟨hy.1, ?_⟩, (physicalSpatialEquiv d).symm_apply_apply y⟩
  exact (show OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ ((physicalSpatialEquiv d y).2) < 0 from hy.2).le

theorem contDiffOn_real_physical_fiber_integral {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {d : ℕ} (a : ℝ) (ha : 0 < a) (τ : E → ℂ) (hτ : ContDiff ℝ ∞ τ)
    (f : E × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3 → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ ∞
      (fun z => ∫ y in physicalSpatialFiber d a (τ z), f (z, y))
      {z | a < ‖τ z‖} := by
  have hL : ContDiff ℝ ∞
      (fun p : (E × (Fin (d + 1) → ℝ)) × (Option (Fin d) → ℂ) =>
        (p.1.1, physicalSpatialEmbedding d p.1.2 p.2)) :=
    (contDiff_fst.comp contDiff_fst).prodMk
      ((contDiff_physicalSpatialEmbedding d ∞).comp
        ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd))
  have hphys := contDiffOn_periodicPhysicalFiberIntegral a ha τ hτ _ (hf.comp hL)
  apply hphys.congr
  intro z hz
  exact physicalSpatialFiber_integral a (τ z) ha (le_of_lt hz)
    (OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded (physicalSpatialFiber_bounded d a (τ z) ha (le_of_lt hz))
      (hf.continuous.comp (continuous_const.prodMk continuous_id)))

end OAI.Analysis.PDE.Green
